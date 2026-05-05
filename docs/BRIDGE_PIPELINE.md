# Bridge pipeline architecture

```mermaid
flowchart TD
    M["mumei .proof-cert.json"] --> I["scripts/ingest_cert.py"]
    I --> C["collect unknown AtomCertificate entries"]
    C --> T["translate requires / ensures"]
    C --> B{"body_expr present?"}
    B -->|simple arithmetic / if / match| D["emit def <atom>Result"]
    B -->|complex or absent| F["contract-only fallback"]
    D --> G["emit theorem with h_body, rw, unfold"]
    F --> H["emit theorem requires -> ensures"]
    G --> L["lake build"]
    H --> L
    L --> E["scripts/export_cert.py"]
    E --> O[".lean-cert.json with lean_verified atoms"]
```

Simple `body_expr` terms let generated theorems prove postconditions
from body semantics before tactic automation runs. Unsupported body
forms remain safe: the bridge keeps the previous contract-only theorem
shape and any unresolved proof still surfaces as a `sorry` warning.
