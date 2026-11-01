#!/usr/bin/env python3
"""Generate or check the CLI reference."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"
for path in (REPO_ROOT, SCRIPTS_DIR):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from cli_reference import render_cli_reference

DEFAULT_OUTPUT = REPO_ROOT / "docs" / "CLI_REFERENCE.md"


def main(
    argv: list[str] | None = None,
    *,
    reference_path: Path | None = None,
) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if arguments not in ([], ["--check"]):
        print("usage: gen_cli_reference.py [--check]", file=sys.stderr)
        return 2
    output = reference_path or DEFAULT_OUTPUT
    rendered = render_cli_reference()
    if arguments == ["--check"]:
        if not output.is_file() or output.read_text(encoding="utf-8") != rendered:
            print(f"{output} is out of date; regenerate with ./scripts/gen_cli_reference.py", file=sys.stderr)
            return 1
        print(f"{output} is up to date")
        return 0
    output.write_text(rendered, encoding="utf-8")
    print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
