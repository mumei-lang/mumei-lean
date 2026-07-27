"""Deterministic candidate-order learning for the automatic tactic search.

The tactic search (``scripts/tactic_search.py``, spec §12) probes a fixed
ladder. Which entry is adopted therefore depends on the ladder order alone,
which makes the search reproducible but also makes it re-probe candidates that
have never closed a goal of the obligation class at hand.

This module adds the only kind of learning that keeps that reproducibility: a
*pinned, version-controlled* record of which candidate previously closed which
``(obligation_class, stage)`` goal, used to deterministically re-rank the ladder
(spec §12.5). No candidate is added or removed by learning, ties keep the
declared ladder order, and the record is only rewritten when a run is asked to
(``bridge.py --record-tactic-search-history``), so an unchanged history file
means an unchanged search.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent

#: Pinned learning artifact. Version-controlled so a checkout fully determines
#: the search order.
HISTORY_PATH = REPO_ROOT / "data" / "tactic_search_history.json"

#: Schema marker written into the artifact.
HISTORY_SCHEMA = "mumei-lean.tactic_search_history/v1"

_UNCLASSIFIED = "unclassified"


def _key(obligation_class: Optional[str], stage: str) -> Tuple[str, str]:
    return (obligation_class or _UNCLASSIFIED, stage)


@dataclass
class TacticSearchHistory:
    """Successful-candidate counts per ``(obligation_class, stage)``."""

    #: ``(obligation_class, stage) -> {candidate_id: successes}``
    successes: Dict[Tuple[str, str], Dict[str, int]] = field(default_factory=dict)
    #: sha256 of the artifact this history was loaded from, ``None`` when empty.
    fingerprint: Optional[str] = None

    @property
    def is_empty(self) -> bool:
        return not self.successes

    def ordered_candidates(
        self,
        candidates: Sequence[Tuple[str, str]],
        *,
        obligation_class: Optional[str],
        stage: str,
    ) -> Tuple[Tuple[str, str], ...]:
        """Re-rank ``candidates`` by past success, keeping ladder order on ties.

        The result is a permutation of ``candidates``: learning never drops or
        invents a candidate, so an entry recorded for a candidate that has since
        left the ladder is simply ignored.
        """
        learned = self.successes.get(_key(obligation_class, stage), {})
        if not learned:
            return tuple(candidates)
        return tuple(
            sorted(
                candidates,
                key=lambda entry: (
                    -learned.get(entry[0], 0),
                    [candidate_id for candidate_id, _ in candidates].index(entry[0]),
                ),
            )
        )

    def record_success(
        self,
        *,
        obligation_class: Optional[str],
        stage: str,
        candidate: str,
    ) -> None:
        bucket = self.successes.setdefault(_key(obligation_class, stage), {})
        bucket[candidate] = bucket.get(candidate, 0) + 1

    def to_payload(self) -> dict:
        """Canonical, deterministically ordered JSON payload."""
        entries: List[dict] = []
        for (obligation_class, stage), bucket in sorted(self.successes.items()):
            for candidate, successes in sorted(bucket.items()):
                entries.append(
                    {
                        "obligation_class": obligation_class,
                        "stage": stage,
                        "candidate": candidate,
                        "successes": successes,
                    }
                )
        return {"schema": HISTORY_SCHEMA, "entries": entries}


def _fingerprint(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def load_history(path: Optional[Path] = None) -> TacticSearchHistory:
    """Load the pinned history; a missing or malformed file learns nothing."""
    history_path = path or HISTORY_PATH
    try:
        payload = json.loads(history_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return TacticSearchHistory()
    if not isinstance(payload, dict) or payload.get("schema") != HISTORY_SCHEMA:
        return TacticSearchHistory()
    history = TacticSearchHistory()
    raw_entries = payload.get("entries")
    if not isinstance(raw_entries, list):
        return TacticSearchHistory()
    for entry in raw_entries:
        if not isinstance(entry, dict):
            continue
        candidate = entry.get("candidate")
        stage = entry.get("stage")
        successes = entry.get("successes")
        if not isinstance(candidate, str) or not isinstance(stage, str):
            continue
        if not isinstance(successes, int) or successes <= 0:
            continue
        obligation_class = entry.get("obligation_class")
        bucket = history.successes.setdefault(
            _key(obligation_class if isinstance(obligation_class, str) else None, stage),
            {},
        )
        bucket[candidate] = bucket.get(candidate, 0) + successes
    history.fingerprint = _fingerprint(history.to_payload())
    return history


def save_history(history: TacticSearchHistory, path: Optional[Path] = None) -> Path:
    """Write ``history`` back to the pinned artifact and refresh its fingerprint."""
    history_path = path or HISTORY_PATH
    history_path.parent.mkdir(parents=True, exist_ok=True)
    payload = history.to_payload()
    history_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    history.fingerprint = _fingerprint(payload)
    return history_path
