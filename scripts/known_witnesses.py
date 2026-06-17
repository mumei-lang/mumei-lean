"""Shared registry for committed Lean witnesses known to the bridge."""
from __future__ import annotations

from pathlib import Path
from typing import Dict, Optional


KNOWN_LEAN_WITNESSES: Dict[str, Dict[str, str]] = {
    "abs_saturating": {
        "module_key": "std/math/abs",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "abs_saturating_correct",
    },
    "fixed_point_abs": {
        "module_key": "std/math/fixed_point",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "fixed_point_abs_correct",
    },
    "fixed_point_from_int": {
        "module_key": "std/math/fixed_point",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "fixed_point_from_int_correct",
    },
    "list_length": {
        "module_key": "std/list",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "list_length_correct",
    },
    "balance_conservation": {
        "module_key": "std/finance/settlement",
        "module": "MumeiLean.Settlement",
        "theorem": "balance_conservation",
    },
    "trace_balance_conservation": {
        "module_key": "std/finance/settlement",
        "module": "MumeiLean.Settlement",
        "theorem": "trace_balance_conservation",
    },
    "no_settlement_without_validate": {
        "module_key": "std/finance/settlement",
        "module": "MumeiLean.Settlement",
        "theorem": "no_settlement_without_validate",
    },
    "no_reentrancy_after_withdraw": {
        "module_key": "std/contract/vault",
        "module": "MumeiLean.SmartContract",
        "theorem": "no_reentrancy_after_withdraw",
    },
    "withdraw_preserves_other_balance": {
        "module_key": "std/contract/vault",
        "module": "MumeiLean.SmartContract",
        "theorem": "withdraw_preserves_other_balance",
    },
    "withdraw_amount_nonnegative_bound": {
        "module_key": "std/contract/vault",
        "module": "MumeiLean.SmartContract",
        "theorem": "withdraw_amount_nonnegative_bound",
    },
    "nlae_vault_withdraw_amount_nonnegative_bound": {
        "module_key": "examples/nlae_integration_demo",
        "module": "MumeiLean.SmartContract",
        "theorem": "nlae_vault_withdraw_amount_nonnegative_bound",
    },
    "nlae_vault_no_negative_withdraw": {
        "module_key": "examples/nlae_integration_demo",
        "module": "MumeiLean.SmartContract",
        "theorem": "nlae_vault_no_negative_withdraw",
    },
    "add_bounded": {
        "module_key": "std/math/patterns",
        "module": "MumeiLean.Patterns",
        "theorem": "add_bounded",
    },
    "transfer_preserves_sum": {
        "module_key": "std/math/patterns",
        "module": "MumeiLean.Patterns",
        "theorem": "transfer_preserves_sum",
    },
}


def _module_to_lean_namespace(module_key: str, prefix: str = "Generated") -> str:
    parts = [p for p in module_key.replace("\\", "/").split("/") if p]
    sanitised: list[str] = []
    for part in parts:
        clean = "".join(c if c.isalnum() or c == "_" else "_" for c in part)
        if not clean:
            clean = "M"
        if clean[0].isdigit():
            clean = "M" + clean
        sanitised.append(clean[:1].upper() + clean[1:])
    return ".".join([prefix] + sanitised) if sanitised else prefix


def known_witness_generated_theorem(atom_name: str) -> Optional[str]:
    witness = KNOWN_LEAN_WITNESSES.get(atom_name)
    if witness is None:
        return None
    namespace = _module_to_lean_namespace(witness["module_key"])
    return f"{namespace}.{atom_name}_correct"


def known_atom_from_generated_theorem(theorem_name: str) -> Optional[str]:
    raw = theorem_name.strip()
    for atom_name in KNOWN_LEAN_WITNESSES:
        if raw == known_witness_generated_theorem(atom_name):
            return atom_name
    return None


def known_witness_proof_path(atom_name: str) -> str:
    witness = KNOWN_LEAN_WITNESSES[atom_name]
    return Path(*witness["module"].split(".")).with_suffix(".lean").as_posix()
