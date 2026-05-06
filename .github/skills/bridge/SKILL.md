---
name: bridge
description: Translate Mumei .proof.json or proof-bundle certificates into Lean 4 theorem files and export .lean-cert.json certificates.
---

Given a Mumei proof certificate, run the mumei-lean bridge from `.proof.json`/`.proof-cert.json` to generated Lean theorem modules and `.lean-cert.json` output.

# Step 1: Prepare proof certificate input

Action:
    Locate a single Mumei proof certificate, proof bundle, or Mumei checkout containing unknown atom certificates.

Expectation:
    Input JSON is valid and contains atom entries, especially atoms whose `z3_check_result` is `unknown`.

Result:
    If input is valid, proceed to Step 2.

```bash
python -m json.tool module.proof-cert.json >/dev/null
```

# Step 2: Run `python bridge.py`

Action:
    Invoke `scripts/bridge.py` with `--cert`, `--bundle`, or `--scan-unknown`.

Expectation:
    The bridge writes generated Lean files under `generated/`, runs `lake build` unless `--no-build` is set, and exports Lean certificate JSON.

Result:
    Generated theorem files and `.lean-cert.json` output exist.

```bash
python scripts/bridge.py \
  --cert module.proof-cert.json \
  --lean-cert-out out/module.lean-cert.json
```

```bash
python scripts/bridge.py \
  --scan-unknown ../mumei \
  --lean-cert-out out/ \
  --summary-json out/summary.json
```

# Step 3: Confirm generated Lean and certificate output

Action:
    Inspect generated `.lean` files and validate the exported `.lean-cert.json`.

Expectation:
    Generated theorems correspond to unknown atoms. Successfully proved atoms are marked `z3_check_result = "lean_verified"` in the exported certificate.

Result:
    Report generated module paths, certificate output, and any unproved atoms or build diagnostics.

```bash
python -m json.tool out/module.lean-cert.json >/dev/null
lake build
```

# Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| cert | path | no | | Single Mumei proof certificate |
| bundle | path | no | | Mumei proof bundle |
| scan_unknown | path | no | | Mumei repo to scan for unknown certs |
| out_dir | path | no | `generated` | Generated Lean output directory |
| lean_cert_out | path | yes unless no-export | | Exported Lean certificate path/directory |
| no_build | flag | no | off | Skip `lake build` for dry-run generation |
