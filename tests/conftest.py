"""Shared pytest setup for mumei-lean Python bridge tests.

The bridge scripts live under ``scripts/`` and are imported as
top-level modules (``ingest_cert``, ``export_cert``, ``bridge``). This
module makes the ``scripts/`` directory importable when running
``pytest`` from the repo root.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))
