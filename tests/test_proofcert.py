"""Regression tests for the proof-certificate enum vocabulary."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from proofcert import VerificationStatus, Z3CheckResult


REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_PATH = REPO_ROOT / "schema" / "proof-cert.schema.json"
FIXTURE_PATH = Path(__file__).resolve().parent / "fixtures" / "abs_saturating.proof-cert.json"


def test_enum_members_match_vendored_schema():
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    assert [member.value for member in Z3CheckResult] == schema["$defs"][
        "z3CheckResult"
    ]["enum"]
    assert [member.value for member in VerificationStatus] == schema["$defs"][
        "verificationStatus"
    ]["enum"]


def test_representative_certificate_validates_against_schema():
    jsonschema = pytest.importorskip("jsonschema")
    draft202012 = jsonschema.Draft202012Validator

    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    cert = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
    for atom in cert.get("atoms", []):
        if isinstance(atom, dict):
            atom["status"] = VerificationStatus.VERIFIED.value
    cert["all_verified"] = True

    draft202012.check_schema(schema)
    draft202012(schema).validate(cert)
