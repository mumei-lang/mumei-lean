"""Shared pytest setup for mumei-lean Python bridge tests.

The bridge scripts live under ``scripts/`` and are imported as
top-level modules (``ingest_cert``, ``export_cert``, ``bridge``). This
module makes the ``scripts/`` directory importable when running
``pytest`` from the repo root.
"""
from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


@pytest.fixture
def lake_available():
    if shutil.which("lake") is None:
        elan_bin = Path.home() / ".elan" / "bin"
        if shutil.which("lake", path=f"{elan_bin}:{os.environ.get('PATH', '')}"):
            os.environ["PATH"] = f"{elan_bin}:{os.environ.get('PATH', '')}"
    if shutil.which("lake") is None:
        pytest.skip("lake not available")
