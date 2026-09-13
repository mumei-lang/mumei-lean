"""Automatic tactic search for residual generated obligations.

`ingest_cert.py` selects a bridge lemma template per obligation class
(`docs/LEAN_TRANSLATOR_SPEC.md` §5). Obligations no template matches either fall
back to the generic ``mumei_arith`` / ``mumei_arith_deep`` cascade or, when the
translator recorded a ``manual_lemma_reason``, are not emitted at all. This
module searches a fixed candidate ladder for a tactic that closes such a
residual goal, so the bridge can adopt it as the generated proof (spec §12).

The search is deterministic and time-bounded:

* all candidates for one obligation are compiled in a single ``lake env lean``
  probe module, so the ladder order alone decides which tactic is adopted;
* the probe compile is bounded by a per-obligation timeout and each candidate by
  ``maxHeartbeats``;
* a candidate counts as successful only when the probe reports neither an error
  nor a ``sorry`` warning inside that candidate's line span.

Adopting a tactic never promotes an atom by itself: the bridge re-renders the
generated module with the adopted tactic and only a successful real ``lake
build`` yields ``lean_verified``. When no candidate succeeds the atom keeps its
``manual_lemma_reason`` verbatim.
"""

from __future__ import annotations

import dataclasses
import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from ingest_cert import (
    IngestedAtom,
    render_theorem,
    uses_generic_fallback_tactic,
)
from tactic_history import TacticSearchHistory

REPO_ROOT = Path(__file__).resolve().parent.parent

#: Ordered candidate ladder (spec §12.2). ``id`` is what lands in metadata,
#: ``tactic`` is the Lean tactic emitted into the generated proof. The first
#: twelve entries cover arithmetic / modular / field goals; the tail widens the
#: ladder to propositional, list, order, inductive and modular-exponentiation
#: goals.
TACTIC_CANDIDATES: Tuple[Tuple[str, str], ...] = (
    ("omega", "omega"),
    ("linarith", "linarith"),
    ("nlinarith", "nlinarith"),
    ("positivity", "positivity"),
    ("norm_num", "norm_num"),
    ("ring", "ring1"),
    ("field_simp", "field_simp"),
    ("decide", "decide"),
    ("simp_arith", "simp_all <;> omega"),
    ("mumei_field", "mumei_field"),
    ("mumei_ff_mod", "mumei_ff_mod"),
    ("aesop", "aesop"),
    ("tauto", "tauto"),
    ("mumei_list", "mumei_list"),
    ("mumei_order", "mumei_order"),
    ("mumei_induct", "mumei_induct"),
    ("mumei_ff_pow", "mumei_ff_pow"),
)

#: Per-candidate heartbeat bound, keeping a single candidate from eating the
#: whole per-obligation budget.
CANDIDATE_MAX_HEARTBEATS = 400000

#: Default per-obligation wall-clock budget for the probe compile, in seconds.
DEFAULT_TACTIC_SEARCH_TIMEOUT_S = 300.0

#: Probe scratch directory, deliberately outside ``generated/`` so ``lake
#: build`` never picks a probe module up as a generated theorem.
PROBE_DIR_NAME = ".tactic_search"

STAGE_RESIDUAL = "residual"
STAGE_BUILD_FAILURE = "build_failure"

_DIAGNOSTIC_RE = re.compile(r"^[^\s]*probe\.lean:(\d+):\d+: (error|warning): (.*)$")


@dataclass
class TacticSearchResult:
    """Outcome of searching the ladder for one obligation."""

    atom_name: str
    stage: str
    adopted_tactic: Optional[str]
    candidates_tried: List[str]
    search_time_s: float
    exhausted: bool
    timed_out: bool
    skipped_reason: Optional[str] = None
    history_ranked: bool = False
    history_fingerprint: Optional[str] = None

    def as_metadata(self) -> dict:
        return {
            "stage": self.stage,
            "adopted_tactic": self.adopted_tactic,
            "candidates_tried": list(self.candidates_tried),
            "search_time_s": round(self.search_time_s, 3),
            "exhausted": self.exhausted,
            "timed_out": self.timed_out,
            "history_ranked": self.history_ranked,
            "history_fingerprint": self.history_fingerprint,
        }


def obligation_class_of(atom: IngestedAtom) -> Optional[str]:
    """Learning key for ``atom`` (spec §12.5).

    The translator's ``obligation_class`` is preferred; certificates whose
    translator IR predates it fall back to the goal's ``logic_fragment_tag``,
    so goals of the same shape share a learned ranking.
    """
    if isinstance(atom.translator_ir, dict):
        obligation_class = atom.translator_ir.get("obligation_class")
        if isinstance(obligation_class, str) and obligation_class:
            return obligation_class
    if atom.logic_fragment_tag:
        return atom.logic_fragment_tag
    return None


def ladder_for(
    atom: IngestedAtom,
    *,
    stage: str,
    history: Optional[TacticSearchHistory] = None,
    candidates: Sequence[Tuple[str, str]] = TACTIC_CANDIDATES,
) -> Tuple[Tuple[str, str], ...]:
    """Ladder to probe for ``atom``, re-ranked by past runs when available."""
    if history is None or history.is_empty:
        return tuple(candidates)
    return history.ordered_candidates(
        candidates,
        obligation_class=obligation_class_of(atom),
        stage=stage,
    )


def is_search_eligible(atom: IngestedAtom, stage: str) -> bool:
    """Whether ``atom`` may be handed to the tactic search (spec §12.1)."""
    if atom.auto_tactic is not None or atom.external_proof is not None:
        return False
    if not atom.has_faithful_statement:
        return False
    if atom.has_custom_bridge_proof:
        return False
    if stage == STAGE_RESIDUAL:
        return atom.manual_lemma_reason is not None
    if stage == STAGE_BUILD_FAILURE:
        return uses_generic_fallback_tactic(atom)
    raise ValueError(f"unknown tactic search stage: {stage}")


def candidate_tactic_block(tactic: str) -> str:
    """Wrap a ladder tactic into the proof body the bridge emits.

    Generated statements are implications (``requires → ensures``), so every
    candidate runs after ``intros``, exactly like the generic ``mumei_arith``
    cascade it replaces.
    """
    return f"(intros; {tactic})"


def _candidate_atom(atom: IngestedAtom, tactic: str) -> IngestedAtom:
    return dataclasses.replace(atom, auto_tactic=candidate_tactic_block(tactic))


def build_probe_module(
    atom: IngestedAtom,
    candidates: Sequence[Tuple[str, str]] = TACTIC_CANDIDATES,
) -> Tuple[str, Dict[str, Tuple[int, int]]]:
    """Render one Lean module probing every candidate for ``atom``.

    Each candidate is rendered by ``render_theorem`` inside its own namespace,
    so a probe success and the final emission agree by construction. Returns
    the module source and a map from candidate id to its ``(first, last)``
    1-based line span.
    """
    lines: List[str] = [
        "import MumeiLean",
        "",
        "open MumeiLean",
        "",
        f"-- tactic search probe for mumei atom `{atom.name}`",
        "",
    ]
    spans: Dict[str, Tuple[int, int]] = {}
    for index, (candidate_id, tactic) in enumerate(candidates):
        namespace = f"TacticProbe{index}"
        start = len(lines) + 1
        lines.append(f"namespace {namespace}")
        lines.append("")
        lines.append(f"set_option maxHeartbeats {CANDIDATE_MAX_HEARTBEATS} in")
        rendered = render_theorem(_candidate_atom(atom, tactic))
        lines.extend(rendered.rstrip("\n").splitlines())
        lines.append("")
        lines.append(f"end {namespace}")
        lines.append("")
        spans[candidate_id] = (start, len(lines))
    return "\n".join(lines) + "\n", spans


def _failed_candidates(
    output: str,
    spans: Dict[str, Tuple[int, int]],
) -> set:
    """Candidate ids whose line span carries an error or ``sorry`` warning."""
    failed = set()
    for raw_line in output.splitlines():
        match = _DIAGNOSTIC_RE.match(raw_line.strip())
        if match is None:
            continue
        line_no = int(match.group(1))
        severity = match.group(2)
        message = match.group(3)
        if severity == "warning" and "sorry" not in message:
            continue
        for candidate_id, (start, end) in spans.items():
            if start <= line_no <= end:
                failed.add(candidate_id)
    return failed


def search_tactic(
    atom: IngestedAtom,
    *,
    stage: str,
    lake_cmd: Sequence[str] = ("lake",),
    probe_dir: Optional[Path] = None,
    timeout_s: float = DEFAULT_TACTIC_SEARCH_TIMEOUT_S,
    candidates: Sequence[Tuple[str, str]] = TACTIC_CANDIDATES,
    history: Optional[TacticSearchHistory] = None,
) -> TacticSearchResult:
    """Search the ladder for a tactic closing ``atom``'s generated goal.

    The atom is left untouched; callers apply ``adopted_tactic`` themselves.
    When ``history`` is given the ladder is re-ranked by past successes for
    this obligation class and stage (spec §12.5); the ranking is a pure
    function of the pinned artifact, so the search stays deterministic.
    """
    started = time.monotonic()
    declared = tuple(candidates)
    # Spec §12.4: the flag reports a ranking that actually moved *this*
    # obligation's ladder, not merely the presence of a history artifact.
    candidates = ladder_for(atom, stage=stage, history=history, candidates=declared)
    history_ranked = candidates != declared
    history_fingerprint = history.fingerprint if history_ranked else None
    if not is_search_eligible(atom, stage):
        return TacticSearchResult(
            atom_name=atom.name,
            stage=stage,
            adopted_tactic=None,
            candidates_tried=[],
            search_time_s=0.0,
            exhausted=False,
            timed_out=False,
            skipped_reason="not_eligible",
            history_ranked=history_ranked,
            history_fingerprint=history_fingerprint,
        )

    candidates = ladder_for(
        atom,
        stage=stage,
        history=history,
        candidates=candidates,
    )
    source, spans = build_probe_module(atom, candidates)
    probe_root = probe_dir or (REPO_ROOT / PROBE_DIR_NAME)
    probe_root.mkdir(parents=True, exist_ok=True)
    probe_path = probe_root / "probe.lean"
    probe_path.write_text(source, encoding="utf-8")

    try:
        proc = subprocess.run(  # noqa: S603 - explicit lake invocation
            [*lake_cmd, "env", "lean", str(probe_path)],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
    except FileNotFoundError:
        return TacticSearchResult(
            atom_name=atom.name,
            stage=stage,
            adopted_tactic=None,
            candidates_tried=[],
            search_time_s=time.monotonic() - started,
            exhausted=False,
            timed_out=False,
            skipped_reason="lake_missing",
            history_ranked=history_ranked,
            history_fingerprint=history_fingerprint,
        )
    except subprocess.TimeoutExpired:
        return TacticSearchResult(
            atom_name=atom.name,
            stage=stage,
            adopted_tactic=None,
            candidates_tried=[candidate_id for candidate_id, _ in candidates],
            search_time_s=time.monotonic() - started,
            exhausted=False,
            timed_out=True,
            history_ranked=history_ranked,
            history_fingerprint=history_fingerprint,
        )

    failed = _failed_candidates(proc.stdout + "\n" + proc.stderr, spans)
    tried: List[str] = []
    for candidate_id, _tactic in candidates:
        tried.append(candidate_id)
        if candidate_id not in failed:
            return TacticSearchResult(
                atom_name=atom.name,
                stage=stage,
                adopted_tactic=candidate_id,
                candidates_tried=tried,
                search_time_s=time.monotonic() - started,
                exhausted=False,
                timed_out=False,
                history_ranked=history_ranked,
                history_fingerprint=history_fingerprint,
            )
    return TacticSearchResult(
        atom_name=atom.name,
        stage=stage,
        adopted_tactic=None,
        candidates_tried=tried,
        search_time_s=time.monotonic() - started,
        exhausted=True,
        timed_out=False,
        history_ranked=history_ranked,
        history_fingerprint=history_fingerprint,
    )


def tactic_for_candidate(candidate_id: str) -> Optional[str]:
    """Lean tactic text for a ladder ``candidate_id``."""
    for known_id, tactic in TACTIC_CANDIDATES:
        if known_id == candidate_id:
            return tactic
    return None


def apply_search_result(
    atom: IngestedAtom,
    result: TacticSearchResult,
) -> IngestedAtom:
    """Return ``atom`` with the adopted tactic applied, if any.

    ``manual_lemma_reason`` is deliberately preserved: it stays in the
    certificate metadata as provenance, and only a successful ``lake build`` of
    the re-rendered module promotes the atom.
    """
    if result.adopted_tactic is None:
        return atom
    tactic = tactic_for_candidate(result.adopted_tactic)
    if tactic is None:
        return atom
    atom.auto_tactic = candidate_tactic_block(tactic)
    return atom
