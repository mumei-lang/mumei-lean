# Lean translator formal specification

This document fixes the formal Mumei-to-Lean 4 lowering contract used by
`scripts/expr_translator.py`, the generated theorem surface, and downstream proof
certificate validation. The rules are intentionally small and auditable: every
`TranslatorIR.lowering_rules` entry emitted by the translator must appear in the
catalog below.

## 1. Type system mapping

Let `⟦T⟧` denote the Lean 4 type assigned to a Mumei type `T`.

| Rule | Mumei type | Lean 4 type | Bridge lemma |
|---|---|---|---|
| `type_system_mapping.i64` | `i64` | `Int` | `mumei_i64_base_bridge` |
| `type_system_mapping.u64` | `u64` | `Nat` | future unsigned scalar bridge |
| `type_system_mapping.f64` | `f64` | `Float` | future floating scalar bridge |
| `type_system_mapping.bool` | `bool` | `Bool` | `mumei_bool_base_bridge` |
| `type_system_mapping.string` | `string` | `String` | `mumei_string_base_bridge` |
| `type_system_mapping.array` | `array<T>` | `List ⟦T⟧` | `mumei_array_bounds_bridge`, `mumei_array_get_bridge` |
| `type_system_mapping.refinement` | `type T where P` | `{v : ⟦T⟧ // P v}` | `mumei_subtype_predicate_bridge` |

Mathematically:

```text
⟦i64⟧ = Int
⟦u64⟧ = Nat
⟦f64⟧ = Float
⟦bool⟧ = Bool
⟦string⟧ = String
⟦array<T>⟧ = List ⟦T⟧
⟦type T where P⟧ = {v : ⟦T⟧ // P v}
```

Lean examples:

```lean
#check (42 : Int)
#check (0 : Nat)
#check (true : Bool)
#check ("mumei" : String)
#check ([1, 2, 3] : List Int)
#check ({v : Int // v ≥ 0} : Type)
```

The Python translator currently emits binder mappings for the supported contract
surface:

```text
i64        -> Int
string     -> String
array<i64> -> List Int
```

Any new `TranslatorIRBinder.mumei_type` must be added to this specification and
to the compliance catalog before it is emitted.

## 2. Refinement type lowering

Mumei refinement syntax:

```text
{v : T | P v}
type T where P
```

lowers to the Lean subtype carrier:

```lean
MumeiSubtype T P
-- definitionally:
{v : T // P v}
```

The value part is projected with `.val`; the proof that the predicate holds is
projected with `.property` / `.2` and preserved by:

```lean
theorem mumei_subtype_predicate_bridge {T : Type u} {P : T → Prop}
    (x : MumeiSubtype T P) : P x.val := x.2
```

Formal rule:

```text
Γ ⊢ e : {v : T | P v}
──────────────────────────── refinement_predicate_lowering
Γ ⊢ mumei_subtype_predicate_bridge e : P e.val
```

This rule is predicate-preserving only; it does not synthesize a new proof of
`P`. The proof must already be carried by the subtype value.

## 3. Contract and expression lowering

A Mumei contract expression `φ` lowers to a Lean proposition `⟦φ⟧ᵖ`.

| Mumei expression | Lean 4 expression |
|---|---|
| `true` | `True` |
| `false` | `False` |
| `a && b` | `⟦a⟧ᵖ ∧ ⟦b⟧ᵖ` |
| `a || b` | `⟦a⟧ᵖ ∨ ⟦b⟧ᵖ` |
| `!a` | `¬ ⟦a⟧ᵖ` |
| `a == b` | `⟦a⟧ = ⟦b⟧` |
| `a != b` | `⟦a⟧ ≠ ⟦b⟧` |
| `a >= b` | `⟦a⟧ ≥ ⟦b⟧` |
| `a <= b` | `⟦a⟧ ≤ ⟦b⟧` |
| `if c then a else b` | `if ⟦c⟧ᵖ then ⟦a⟧ else ⟦b⟧` |
| `match x { p => e, _ => d }` | `match ⟦x⟧ with | p => ⟦e⟧ | _ => ⟦d⟧` |

Known helper calls lower as follows:

| Mumei call | Lean 4 call |
|---|---|
| `len(x)` | `mumei_len ⟦x⟧` |
| `abs(x)` | `mumei_abs ⟦x⟧` |
| `min(a, b)` | `min ⟦a⟧ ⟦b⟧` |
| `max(a, b)` | `max ⟦a⟧ ⟦b⟧` |
| `old(x)` | `old_x` |
| `starts_with(s, p)` | `mumei_starts_with ⟦s⟧ ⟦p⟧` |
| `ends_with(s, p)` | `mumei_ends_with ⟦s⟧ ⟦p⟧` |
| `contains(s, p)` | `mumei_contains ⟦s⟧ ⟦p⟧` |
| `not_contains(s, p)` | `mumei_not_contains ⟦s⟧ ⟦p⟧` |
| `sum(arr, n)` | `mumei_sum ⟦arr⟧ ⟦n⟧` |
| `count(arr, v)` | `mumei_count ⟦arr⟧ ⟦v⟧` |
| `mod(a, b)` | `MumeiLean.CryptoHelpers.mumei_mod ⟦a⟧ ⟦b⟧` |
| `pow(a, b)` | `MumeiLean.CryptoHelpers.mumei_pow ⟦a⟧ ⟦b⟧` |
| `phi(n)` | `MumeiLean.CryptoHelpers.mumei_phi ⟦n⟧` |

Array access is guarded by the array bridge catalog:

```text
arr[i] -> arr.get! i.toNat
```

A proof-producing path should prefer the guarded form:

```lean
mumei_array_get arr i h
```

where `h : i < arr.length`; `mumei_array_get_bridge` records that this is the
same as Lean's dependent `List.get`.

## 4. Loop invariant and recursion encoding

Mumei loop invariants are encoded as Lean propositions over explicit integer
indices. The translator uses quantifier lowering instead of an operational loop
semantics.

### 4.1 Bounded quantifier

Mumei:

```text
forall(i, start, end, body)
```

Lean:

```lean
(∀ i : Int, start ≤ i → i < end → body)
```

Formal rule:

```text
⟦forall(i, start, end, body)⟧ᵖ
  = (∀ i : Int, ⟦start⟧ ≤ i → i < ⟦end⟧ → ⟦body⟧ᵖ)
```

This is the canonical encoding for loop invariants such as:

```text
forall(i, 0, n, arr[i] >= 0)
```

which lowers to:

```lean
(∀ i : Int, 0 ≤ i → i < n → arr.get! i.toNat ≥ 0)
```

### 4.2 Unbounded quantifier

Mumei:

```text
forall var: body
```

Lean:

```lean
(∀ var : Int, body)
```

Formal rule:

```text
⟦forall var: body⟧ᵖ = (∀ var : Int, ⟦body⟧ᵖ)
```

The existential counterpart is:

```text
exists var: body -> (∃ var : Int, ⟦body⟧ᵖ)
```

### 4.3 Recursion obligations

Recursive functions and loops are represented as ordinary Lean theorem
obligations plus explicit hypotheses:

```lean
∀ state : S, invariant state → decreases next state state → invariant (next state)
```

The translator does not synthesize termination proofs. It preserves the logical
shape needed by handwritten Lean witnesses, and any unsupported recursion-specific
syntax must be emitted as `manual_lemma_required` metadata.

## 5. Typed intermediate translator IR

`TranslatorIR` is the typed audit record emitted beside each translated theorem.

```python
@dataclass
class TranslatorIR:
    sort: str
    binders: List[TranslatorIRBinder]
    theorem_goal: str
    provenance_span: TranslatorIRProvenanceSpan
    lowering_rules: List[str]
    manual_lemma_reason: Optional[str]
```

### 5.1 `TranslatorIRBinder`

A binder records how one Mumei identifier is represented in Lean.

```python
@dataclass
class TranslatorIRBinder:
    mumei_name: str
    lean_name: str
    mumei_type: str
    lean_type: str
    role: str = "free"
    refinement: Optional[str] = None
```

Roles:

| Role | Meaning |
|---|---|
| `free` | Free identifier from `requires`, `ensures`, or `body_expr` theorem goal. |
| `result` | The theorem result value, normally bound as `result : Int`. |
| `old` | Snapshot of a pre-state value emitted by `old(x)` as `old_x`. |
| `quantifier` | Local Lean binder introduced by `forall` / `exists`; not emitted as a theorem parameter. |
| `refinement_witness` | Subtype value carrying both `.val` and predicate proof. |

Every binder must satisfy:

```text
binder.lean_type = ⟦binder.mumei_type⟧
```

except where a future spec revision explicitly defines a contextual lowering.

## 6. `lowering_rules` catalog

The following rule IDs are currently part of the formal specification and may be
emitted in `TranslatorIR.lowering_rules`.

| Rule ID | Required when | Specification section |
|---|---|---|
| `type_system_mapping` | Any typed binder is emitted. | §1 |
| `contract_lowering` | Any `requires` / `ensures` expression is translated. | §3 |
| `array_bounds_bridge` | Array/list access or array-typed binder appears. | §1, §3 |
| `string_regex_bridge` | String predicate or regex bridge obligation appears. | §1, §3 |
| `refinement_predicate_lowering` | Refinement predicate or quantifier predicate preservation is required. | §2, §4 |
| `integer_overflow_bridge` | Integer arithmetic needs explicit machine-range assumptions. | §1, §3 |

A translator implementation is compliant iff:

1. Every emitted `lowering_rules` entry is listed in this catalog.
2. Every `TranslatorIRBinder` satisfies the type mapping in §1.
3. Unsupported constructs are not silently accepted; they are marked with
   `manual_lemma_reason` and surfaced as warnings or generated theorem TODOs.

`validate_translator_ir_compliance()` enforces these checks at translation time
with warnings only. Warnings do not abort translation, because incomplete Lean
obligations are still useful for triage and handwritten proof completion.
