"""Build a Lean 4 executable and pair it with a Lean proof certificate."""
from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Optional


class LeanExecutableError(RuntimeError):
    """Raised when the Lean executable pipeline cannot complete."""


def _module_to_default_target(module: str) -> str:
    """Derive a Lake executable target from the final Lean module segment."""
    leaf = module.rsplit(".", 1)[-1]
    words = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1-\2", leaf)
    words = re.sub(r"([a-z0-9])([A-Z])", r"\1-\2", words).replace("_", "-")
    return words.lower()


def _lake_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.exists():
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    return env


def _run_lake_build(
    project_dir: Path,
    target: str,
    lake: str,
    env: dict[str, str],
) -> subprocess.CompletedProcess[str]:
    if shutil.which(lake, path=env.get("PATH")) is None:
        raise LeanExecutableError(f"`{lake}` not found on PATH")
    return subprocess.run(  # noqa: S603 - explicit Lake command from CLI arg.
        [lake, "build", target],
        cwd=project_dir,
        capture_output=True,
        text=True,
        env=env,
    )


def _run_lake_update(
    project_dir: Path,
    lake: str,
    env: dict[str, str],
) -> subprocess.CompletedProcess[str]:
    if shutil.which(lake, path=env.get("PATH")) is None:
        raise LeanExecutableError(f"`{lake}` not found on PATH")
    return subprocess.run(  # noqa: S603 - explicit Lake command from CLI arg.
        [lake, "update"],
        cwd=project_dir,
        capture_output=True,
        text=True,
        env=env,
    )


def _ensure_lake_manifest(project_dir: Path, lake: str, env: dict[str, str]) -> None:
    if (project_dir / "lake-manifest.json").exists():
        return
    proc = _run_lake_update(project_dir, lake, env)
    if proc.returncode != 0:
        output = (proc.stdout + proc.stderr).strip()
        detail = f"\n{output}" if output else ""
        raise LeanExecutableError(
            f"`{lake} update` failed with exit code {proc.returncode}{detail}"
        )


def _built_binary_path(project_dir: Path, target: str) -> Path:
    bin_dir = project_dir / ".lake" / "build" / "bin"
    candidates = [bin_dir / target, bin_dir / f"{target}.exe"]
    for candidate in candidates:
        if candidate.exists() and candidate.is_file():
            return candidate
    expected = ", ".join(str(candidate) for candidate in candidates)
    raise LeanExecutableError(f"Lake build succeeded but no binary was found at {expected}")


def _run_binary_smoke_test(binary: Path, args: list[str], timeout: int) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(  # noqa: S603 - binary path is produced by Lake in this script.
        [str(binary), *args],
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if proc.returncode != 0:
        output = (proc.stdout + proc.stderr).strip()
        detail = f"\n{output}" if output else ""
        raise LeanExecutableError(
            f"`{binary} {' '.join(args)}` failed with exit code {proc.returncode}{detail}"
        )
    return proc


def build_executable(
    *,
    project_dir: Path,
    module: str,
    out_dir: Path,
    target: Optional[str] = None,
    cert: Optional[Path] = None,
    binary_name: Optional[str] = None,
    lake: str = "lake",
    run_args: Optional[list[str]] = None,
    run_timeout: int = 30,
) -> tuple[Path, Path]:
    """Compile ``module`` through Lake and copy binary + certificate to ``out_dir``."""
    project_dir = project_dir.resolve()
    out_dir = out_dir.resolve()
    target = target or _module_to_default_target(module)
    cert = cert or (project_dir / ".lean-cert.json")

    if not project_dir.exists():
        raise LeanExecutableError(f"project directory does not exist: {project_dir}")
    if not (project_dir / "lakefile.lean").exists():
        raise LeanExecutableError(f"missing lakefile.lean in {project_dir}")
    if not cert.exists():
        raise LeanExecutableError(f"Lean certificate not found: {cert}")

    env = _lake_env()
    _ensure_lake_manifest(project_dir, lake, env)
    proc = _run_lake_build(project_dir, target, lake, env)
    if proc.returncode != 0:
        output = (proc.stdout + proc.stderr).strip()
        detail = f"\n{output}" if output else ""
        raise LeanExecutableError(
            f"`{lake} build {target}` failed with exit code {proc.returncode}{detail}"
        )

    binary = _built_binary_path(project_dir, target)
    out_dir.mkdir(parents=True, exist_ok=True)
    copied_binary = out_dir / (binary_name or binary.name)
    copied_cert = out_dir / cert.name
    shutil.copy2(binary, copied_binary)
    shutil.copy2(cert, copied_cert)
    copied_binary.chmod(copied_binary.stat().st_mode | 0o111)
    if run_args is not None:
        _run_binary_smoke_test(copied_binary, run_args, run_timeout)
    return copied_binary, copied_cert


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Compile a Lean 4 executable and copy its .lean-cert.json."
    )
    parser.add_argument(
        "--project-dir",
        type=Path,
        default=Path("."),
        help="Lean/Lake project directory containing lakefile.lean.",
    )
    parser.add_argument(
        "--module",
        required=True,
        help="Lean module root used by the executable target, e.g. SimpleCli.",
    )
    parser.add_argument(
        "--target",
        help="Lake executable target. Defaults to the kebab-case module leaf.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        required=True,
        help="Directory that receives the executable and .lean-cert.json.",
    )
    parser.add_argument(
        "--cert",
        type=Path,
        help="Certificate to copy. Defaults to <project-dir>/.lean-cert.json.",
    )
    parser.add_argument(
        "--binary-name",
        help="Optional output filename for the copied executable.",
    )
    parser.add_argument("--lake", default="lake", help="Lake command to invoke.")
    parser.add_argument(
        "--run-args",
        nargs=argparse.REMAINDER,
        help="Optional smoke-test arguments to pass to the copied executable.",
    )
    parser.add_argument(
        "--run-timeout",
        type=int,
        default=30,
        help="Timeout in seconds for --run-args smoke test.",
    )
    return parser


def main(argv: Optional[list[str]] = None) -> int:
    args = _parser().parse_args(argv)
    try:
        binary, cert = build_executable(
            project_dir=args.project_dir,
            module=args.module,
            out_dir=args.out_dir,
            target=args.target,
            cert=args.cert,
            binary_name=args.binary_name,
            lake=args.lake,
            run_args=args.run_args,
            run_timeout=args.run_timeout,
        )
    except LeanExecutableError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    print(f"wrote executable: {binary}")
    print(f"wrote certificate: {cert}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
