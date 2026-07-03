"""Metrics and summary helpers for the bridge pipeline."""
from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Tuple

try:
    from .export_cert import LEAN_VERIFIED, MANUAL_LEMMA_REQUIRED
    from .ingest_cert import IngestedAtom
except ImportError:  # pragma: no cover - direct ``python scripts/bridge.py``
    from export_cert import LEAN_VERIFIED, MANUAL_LEMMA_REQUIRED  # type: ignore
    from ingest_cert import IngestedAtom  # type: ignore


def _empty_metric_bucket() -> dict:
    return {
        "attempts": 0,
        "lean_successes": 0,
        "partial_translation": 0,
        MANUAL_LEMMA_REQUIRED: 0,
        "stale_translator": 0,
        "success_rate": 0.0,
    }


def _metric_bucket_success_rate(bucket: dict) -> None:
    attempts = bucket["attempts"]
    bucket["success_rate"] = (
        round(bucket["lean_successes"] / attempts, 4) if attempts else 0.0
    )


def _aggregate_metrics(
    metadata_by_payload: List[Dict[str, dict]],
    atoms_per_payload: List[List[IngestedAtom]],
) -> dict:
    metrics = {
        "escalation_attempts": 0,
        "lean_successes": 0,
        "partial_translation": 0,
        MANUAL_LEMMA_REQUIRED: 0,
        "stale_translator": 0,
        "by_atom": {},
        "by_logic_fragment": {},
        "by_failure_reason": {},
        "by_z3_result_class": {},
        "low_success_categories": [],
    }
    for metadata, atoms in zip(metadata_by_payload, atoms_per_payload):
        for atom in atoms:
            status = metadata.get(atom.name, {}).get("status", MANUAL_LEMMA_REQUIRED)
            if status == "manual_required":
                status = MANUAL_LEMMA_REQUIRED
            metrics["escalation_attempts"] += 1
            if status == LEAN_VERIFIED:
                metrics["lean_successes"] += 1
            elif status == "partial_translation":
                metrics["partial_translation"] += 1
                if atom.manual_lemma_reason:
                    metrics[MANUAL_LEMMA_REQUIRED] += 1
            elif status == "stale_translator":
                metrics["stale_translator"] += 1
            else:
                metrics[MANUAL_LEMMA_REQUIRED] += 1
            metrics["by_atom"][atom.name] = {
                "status": status,
                "failure_reason": atom.escalation_reason,
                "logic_fragment_tags": atom.logic_fragment_tags,
                "z3_result_class": atom.z3_result_class,
                "translator_version": atom.translator_version,
                "bridge_lemma_hash": atom.bridge_lemma_hash,
                "manual_lemma_reason": atom.manual_lemma_reason,
                "known_witness_used": bool(metadata.get(atom.name, {}).get("known_witness_used")),
                "lean_module": metadata.get(atom.name, {}).get("lean_module"),
                "lean_theorem_name": metadata.get(atom.name, {}).get("lean_theorem_name"),
            }
            reason = atom.escalation_reason or "unknown"
            reason_bucket = metrics["by_failure_reason"].setdefault(
                reason,
                _empty_metric_bucket(),
            )
            reason_bucket["attempts"] += 1
            reason_bucket_key = (
                "lean_successes" if status == LEAN_VERIFIED else status
            )
            reason_bucket[reason_bucket_key] += 1
            for tag in atom.logic_fragment_tags or ["untagged"]:
                tag_bucket = metrics["by_logic_fragment"].setdefault(
                    tag,
                    _empty_metric_bucket(),
                )
                tag_bucket["attempts"] += 1
                tag_bucket_key = (
                    "lean_successes" if status == LEAN_VERIFIED else status
                )
                tag_bucket[tag_bucket_key] += 1
            class_bucket = metrics["by_z3_result_class"].setdefault(
                atom.z3_result_class or atom.z3_check_result,
                _empty_metric_bucket(),
            )
            class_bucket["attempts"] += 1
            class_bucket_key = (
                "lean_successes" if status == LEAN_VERIFIED else status
            )
            class_bucket[class_bucket_key] += 1
    for grouping_name in (
        "by_failure_reason",
        "by_logic_fragment",
        "by_z3_result_class",
    ):
        for key, bucket in metrics[grouping_name].items():
            _metric_bucket_success_rate(bucket)
            if bucket["attempts"] >= 1 and bucket["success_rate"] < 0.7:
                metrics["low_success_categories"].append(
                    {"group": grouping_name, "category": key, **bucket}
                )
    return metrics


def _summary_details(
    payloads: List[Tuple[Path, dict]],
    metadata_by_payload: List[Dict[str, dict]],
    atoms_per_payload: List[List[IngestedAtom]],
) -> List[dict]:
    details: List[dict] = []
    for (src_path, _payload), metadata, atoms in zip(
        payloads,
        metadata_by_payload,
        atoms_per_payload,
    ):
        proved = sum(
            1
            for atom in atoms
            if metadata.get(atom.name, {}).get("status") == LEAN_VERIFIED
        )
        known_witness_used = sum(
            1
            for atom in atoms
            if metadata.get(atom.name, {}).get("known_witness_used")
        )
        details.append(
            {
                "source": str(src_path),
                "candidate_count": len(atoms),
                "lean_fallback": {
                    "attempted": len(atoms),
                    "proved": proved,
                    "known_witness_used": known_witness_used,
                },
            }
        )
    return details
