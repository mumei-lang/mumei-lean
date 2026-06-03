# Mathlib4 integration design

`mumei-lean` remains an escalation backend: Z3 keeps handling the decidable
fragment, and Lean/mathlib4 is used when certificates contain atoms whose
contracts need richer quantifier, algebra, finite-field, or group reasoning.

## Scope

| Mumei contract surface | Lean/mathlib4 target | Status |
|------------------------|----------------------|--------|
| Bounded quantifiers `forall(i, lo, hi, P)` / `exists(i, lo, hi, P)` | `Finset.Ico lo.toNat hi.toNat` plus an `Int.ofNat` binder bridge | Prototype helper in `translate_bounded_quantifier_to_finset` |
| Unbounded quantifiers `forall x: P` / `exists x: P` | Lean dependent binders over translated scalar types | Existing translator path |
| Finite-field helpers `ff_add`, `ff_mul`, `ff_inv`, `ff_eq`, ... | `MumeiLean.Algebra` wrappers backed by `ZMod`, `Int.ModEq`, and closure lemmas | Existing bridge helpers |
| Group helpers `group_mul`, `group_inv`, `group_identity`, ... | `MumeiLean.Algebra` wrappers and mathlib `Group` lemmas | Existing bridge helpers |
| Crypto primitive contracts | Domain-specific bridge lemmas over hash/signature/field helpers | Existing reusable patterns, still manual-lemma-heavy |

## Quantifier translation strategy

### Bounded quantifiers

Default lowering keeps the shape close to Mumei and Z3:

```lean
∀ i : Int, lo ≤ i → i < hi → P i
```

The mathlib4 path is opt-in because it changes the induction/enumeration shape:

```lean
∀ iNat ∈ Finset.Ico lo.toNat hi.toNat,
  let i : Int := Int.ofNat iNat
  P i
```

This gives Lean access to the `Finset` API (`card`, `sum`, membership lemmas,
finite enumeration, induction over ranges) while preserving the Mumei-facing
body variable as `Int`. The bridge lemma obligation is explicit in
`TranslatorIR.requires_bridge_lemmas` as
`mumei_finset_bounded_quantifier_bridge`.

Use this path for:

- finite enumeration proofs where `Finset` induction or cardinality lemmas help;
- contracts involving sums/counts over bounded integer ranges;
- obligations that Z3 reports as `unknown` because the quantified domain must be
  explored structurally.

Keep the default guarded-`Int` path for simple arithmetic invariants so Lean
does not need extra `Nat`/`Int` coercion bookkeeping.

### Unbounded quantifiers

Unbounded quantifiers stay as direct Lean binders:

```lean
∀ x : Int, P x
∃ x : Int, P x
```

They should be routed to manual/domain lemmas unless a later frontend pass can
derive a finite domain or a stronger type (for example a `Finset`, subtype, or
finite group carrier).

## Finite-field strategy

Mumei contract helpers are lowered through stable bridge functions:

```text
ff_add(a, b, p)  →  MumeiLean.Algebra.mumei_ff_add a b p
ff_mul(a, b, p)  →  MumeiLean.Algebra.mumei_ff_mul a b p
ff_eq(a, b, p)   →  MumeiLean.Algebra.mumei_ff_eq a b p
```

The public contract surface remains `Int`-based to match proof certificates and
compiler output. `MumeiLean.Algebra` provides the mathlib-backed proof layer:

- `ZMod` witnesses (`MumeiFF p`) for field-style reasoning;
- closure lemmas such as `ff_add_in_field` and `ff_mul_in_field`;
- modular equality through `Int.ModEq`.

Future lowering can add a certificate flag that chooses direct `ZMod p`
theorem statements when the certificate proves `p` is prime and all operands are
already range-checked.

## Group theory strategy

Group helper calls lower to `MumeiLean.Algebra` names:

```text
group_mul(a, b)      → MumeiLean.Algebra.mumei_group_mul a b
group_inv(a)         → MumeiLean.Algebra.mumei_group_inv a
group_identity()     → MumeiLean.Algebra.mumei_group_identity
```

For abstract proofs, generated Lean should prefer mathlib typeclass statements:

```lean
{G : Type u} [Group G] → (a * a⁻¹ = 1)
```

The Int-backed helpers remain a compatibility layer for current certificates.
When a future Mumei type can express a finite or abstract group carrier, the
translator can emit typeclass-backed theorem goals instead of Int wrappers.

## Crypto primitive proof pattern

Cryptographic primitives should not be proven by expanding runtime
implementations. The bridge should instead prove structural contract facts:

1. parse the certificate atom into a named crypto obligation;
2. lower field/group arithmetic through `MumeiLean.Algebra`;
3. discharge format/range/equality properties with reusable lemmas;
4. record unmodeled cryptographic assumptions as explicit manual lemma reasons.

This keeps the certificate honest: mathlib proves the algebraic scaffolding, and
the remaining cryptographic hardness assumption is visible in metadata rather
than hidden inside generated code.

## Prototype API

`scripts.expr_translator` exposes the active integration points:

- `translate_quantifier(...)` for the existing direct binder lowering;
- `translate_bounded_quantifier_to_finset(...)` for the new Finset prototype;
- `translate_finite_field(...)` for finite-field helper calls;
- `translate_group_theory(...)` for group helper calls.

The prototype deliberately leaves default translation unchanged. Callers can opt
into Finset lowering only for atoms that benefit from mathlib finite-domain
reasoning.
