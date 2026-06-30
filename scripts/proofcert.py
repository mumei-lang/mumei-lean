"""Canonical proof-certificate enum vocabulary for mumei-lean."""

from __future__ import annotations

from enum import Enum


class Z3CheckResult(str, Enum):
    UNSAT = "unsat"
    SAT = "sat"
    UNKNOWN = "unknown"
    SKIPPED = "skipped"
    LEAN_VERIFIED = "lean_verified"


class VerificationStatus(str, Enum):
    VERIFIED = "verified"
    FAILED = "failed"
    SKIPPED = "skipped"
    TRUSTED = "trusted"
    ESCALATION_CANDIDATE = "escalation_candidate"
