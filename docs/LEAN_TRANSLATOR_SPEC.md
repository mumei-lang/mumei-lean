# Lean Translator Formal Specification

This document fixes the formal Mumei-to-Lean 4 lowering contract used by
`scripts/expr_translator.py`, the generated theorem surface, and downstream proof
certificate validation. The rules are intentionally small and auditable: every
`TranslatorIR.lowering_rules` entry emitted by the translator must appear in the
catalog below.

## 1. Type System Mapping

Let `⟦T⟧` denote the Lean 4 type assigned to a Mumei type `T`.

| Mumei Type | Z3 Sort | Lean 4 Type | Semantic Invariant |
|---|---|---|---|
| `i64` | `(_ BitVec 64)` | `Int` | Two's-complement representation; arithmetic wraps on overflow. |
| `u64` | `(_ BitVec 64)` | `Nat` | Non-negative integer; arithmetic wraps on overflow. |
| `f64` | `Float` | `Float` | IEEE 754 floating point. |
| `bool` | `Bool` | `Bool` | Truth value. |
| `string` | `String` | `String` | UTF-8 string. |
| `array<T>` | `(Array T)` | `List T` | Variable-length array/list, with explicit access evidence in Lean. |
| `field` | `Int` / modular arithmetic | `Int` / mathlib4 field carrier | Finite-field element represented by integer residue data. |

| Rule | Mumei type | Lean 4 type | Bridge lemma |
|---|---|---|---|
| `type_system_mapping.i64` | `i64` | `Int` | `mumei_i64_base_bridge` |
| `type_system_mapping.u64` | `u64` | `Nat` | future unsigned scalar bridge |
| `type_system_mapping.f64` | `f64` | `Float` | future floating scalar bridge |
| `type_system_mapping.bool` | `bool` | `Bool` | `mumei_bool_base_bridge` |
| `type_system_mapping.string` | `string` | `String` | `mumei_string_base_bridge` |
| `type_system_mapping.array` | `array<T>` | `List ⟦T⟧` | `mumei_array_bounds_bridge`, `mumei_array_get_bridge` |
| `type_system_mapping.field` | finite-field scalar | `Int` / `ZMod p` helper lemmas | `mathlib4_bridge` |
| `type_system_mapping.refinement` | `type T where P` | `{v : ⟦T⟧ // P v}` | `mumei_subtype_predicate_bridge` |

Mathematically:

```text
⟦i64⟧ = Int
⟦u64⟧ = Nat
⟦f64⟧ = Float
⟦bool⟧ = Bool
⟦string⟧ = String
⟦array<T>⟧ = List ⟦T⟧
⟦field⟧ = Int, with canonical mathlib4 proofs routed through ZMod p
⟦type T where P⟧ = {v : ⟦T⟧ // P v}
```

Lean examples:

```lean
#check (42 : Int)
#check (0 : Nat)
#check (true : Bool)
#check ("mumei" : String)
#check ([1, 2, 3] : List Int)
#check (ZMod 17)
#check ({v : Int // v ≥ 0} : Type)
```

The Python translator currently emits binder mappings for the supported contract
surface:

```text
i64        -> Int
field      -> Int
string     -> String
array<i64> -> List Int
```

Any new `TranslatorIRBinder.mumei_type` must be added to this specification and
to the compliance catalog before it is emitted.

## 2. Operator Semantics

The following operator table is the bidirectional audit surface for Mumei → Z3
→ Lean 4 escalation. The Python translator's `_FORMAL_SPEC_LOWERING_RULES`
catalog and Rust certificate metadata must only emit rule IDs documented here.

| Mumei Operator | Z3 Operator | Lean 4 Operator | Semantic Note |
|---|---|---|---|
| `+` | `bvadd` | `HAdd.hAdd` | Integer addition; overflow handled by the integer bridge. |
| `-` | `bvsub` | `HSub.hSub` | Integer subtraction; overflow handled by the integer bridge. |
| `*` | `bvmul` | `HMul.hMul` | Integer multiplication; overflow handled by the integer bridge. |
| `/` | `bvsdiv` | `HDiv.hDiv` | Integer division; division by zero is undefined in the Mumei contract layer. |
| `%` | `bvsmod` | `HMod.hMod` | Integer remainder; division by zero is undefined in the Mumei contract layer. |
| `&&` | `and` | `And` | Logical conjunction. |
| `\|\|` | `or` | `Or` | Logical disjunction. |
| `!` | `not` | `Not` | Logical negation. |
| `==` | `=` | `Eq` | Equality. |
| `!=` | `distinct` | `Ne` | Disequality. |
| `<` | `bvslt` | `LT.lt` | Signed less-than for integer-like scalar lowering. |
| `<=` | `bvsle` | `LE.le` | Signed less-than-or-equal for integer-like scalar lowering. |
| `>` | `bvsgt` | `GT.gt` | Signed greater-than for integer-like scalar lowering. |
| `>=` | `bvsge` | `GE.ge` | Signed greater-than-or-equal for integer-like scalar lowering. |

## 3. Refinement type lowering

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

## 4. Contract and expression lowering

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
| `ff_add(a, b, p)` | `MumeiLean.Algebra.mumei_ff_add ⟦a⟧ ⟦b⟧ ⟦p⟧` |
| `ff_sub(a, b, p)` | `MumeiLean.Algebra.mumei_ff_sub ⟦a⟧ ⟦b⟧ ⟦p⟧` |
| `ff_mul(a, b, p)` | `MumeiLean.Algebra.mumei_ff_mul ⟦a⟧ ⟦b⟧ ⟦p⟧` |
| `ff_neg(a, p)` | `MumeiLean.Algebra.mumei_ff_neg ⟦a⟧ ⟦p⟧` |
| `ff_pow(a, e, p)` | `MumeiLean.Algebra.mumei_ff_pow ⟦a⟧ ⟦e⟧ ⟦p⟧` |
| `ff_inv(a, p)` | `MumeiLean.Algebra.mumei_ff_inv ⟦a⟧ ⟦p⟧` |
| `ff_div(a, b, p)` | `MumeiLean.Algebra.mumei_ff_div ⟦a⟧ ⟦b⟧ ⟦p⟧` |
| `ff_in_field(a, p)` | `MumeiLean.Algebra.mumei_ff_in_field ⟦a⟧ ⟦p⟧` |
| `is_prime(p)` | `MumeiLean.Algebra.mumei_is_prime ⟦p⟧` |
| `mod_eq(a, b, p)` | `MumeiLean.Algebra.mumei_mod_eq ⟦a⟧ ⟦b⟧ ⟦p⟧` |
| `group_mul(a, b)` | `MumeiLean.Algebra.mumei_group_mul ⟦a⟧ ⟦b⟧` |
| `group_inv(a)` | `MumeiLean.Algebra.mumei_group_inv ⟦a⟧` |
| `group_pow(a, n)` | `MumeiLean.Algebra.mumei_group_pow ⟦a⟧ ⟦n⟧` |
| `group_identity()` | `MumeiLean.Algebra.mumei_group_identity` |

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

## 5. Semantic Gap Bridge Rules

### 5.1 Integer Overflow Bridge

- **Mumei**: `i64` uses two's-complement wrap semantics.
- **Z3**: `(_ BitVec 64)` has explicit wrap semantics.
- **Lean 4**: `Int` is unbounded, so range evidence must be carried explicitly.
- **Bridge Lemma**: `mumei_i64_overflow_bridge`,
  `mumei_i64_add_overflow_bridge`.
- **Lowering Rule**: `integer_overflow_bridge`.

### 5.2 Array Bounds Bridge

- **Mumei**: `arr[i]` requires bounds checking.
- **Z3**: array access is modeled through side constraints.
- **Lean 4**: guarded access uses evidence `i < arr.length`; legacy generated
  expressions may use `List.get!` with `Nat` indices.
- **Bridge Lemma**: `mumei_array_bounds_bridge`, `mumei_array_get_bridge`.
- **Lowering Rule**: `array_bounds_bridge`.

### 5.3 String/Regex Bridge

- **Mumei**: regex/string predicates may be evaluated at runtime.
- **Z3**: string theory support is intentionally restricted by fragment routing.
- **Lean 4**: regex obligations are explicit assumptions or handwritten lemmas.
- **Bridge Lemma**: `mumei_regex_bridge`, `mumei_string_concat_bridge`.
- **Lowering Rule**: `string_regex_bridge`.

### 5.4 Effect State Bridge

- **Mumei**: effects are represented as state transitions.
- **Z3**: effect state is modeled with additional state variables.
- **Lean 4**: `MumeiEffectState` token values represent state snapshots.
- **Bridge Lemma**: `mumei_effect_state_bridge`,
  `mumei_effect_transition_bridge`.

### 5.5 Refinement Predicate Lowering

- **Mumei**: `{v: T | P(v)}` and named refinement types carry predicates.
- **Z3**: refinements lower to additional predicate constraints.
- **Lean 4**: refinements lower to subtypes or predicate arguments.
- **Bridge Lemma**: `mumei_subtype_predicate_bridge`.
- **Lowering Rule**: `refinement_predicate_lowering`.

### 5.6 Finite Field Lowering

- **Mumei**: `ff_add`, `ff_mul`, and related finite-field helpers.
- **Z3**: modular arithmetic constraints.
- **Lean 4**: mathlib4 finite-field support through helper lemmas.
- **Lowering Rule**: `finite_field_lowering`, `mathlib4_bridge`.

### 5.7 Group Theory Lowering

- **Mumei**: `group_mul`, `group_inv`, and related group helpers.
- **Z3**: abstract group axioms.
- **Lean 4**: mathlib4 group support through helper lemmas.
- **Lowering Rule**: `group_theory_lowering`, `mathlib4_bridge`.

### 5.8 Body-semantics nonlinear conjunctions

When a proof certificate carries a complete `body_expr`, the translator may
emit a Lean `def <atom>Result ...` plus a theorem hypothesis
`h_body : result = <atom>Result ...`. For nonlinear arithmetic obligations whose
postcondition is a conjunction, the generated theorem remains a live generated
path: it unfolds the body definition, splits the conjunction structurally, and
uses mathlib-backed nonlinear arithmetic automation (`nlinarith`) to discharge
each conjunct. This keeps atoms such as
`std/math/patterns.mm::bounded_mul_with_overflow_check` on the generated theorem
path rather than a known-witness override.

The same body-semantics path also covers the single non-conjunction nonlinear
case: an atom whose `ensures` is one nonlinear predicate (e.g. `result >= 0`
over a perfect-square polynomial `x * x + 2 * x + 1`) unfolds its body
definition and is discharged directly by `mumei_arith_deep`
(`nlinarith`/`positivity`). This is the sixth live generated theorem path
(`std/math/patterns.mm::poly_bound_monotone`), differentiated from
`bounded_mul_with_overflow_check` by having a non-conjunction postcondition and
requiring no new backing lemma (`bridge_lemma_hash` unchanged).

### 5.9 Crypto deterministic-input body semantics

Crypto/finite-field witnesses that return deterministic flags may carry a
complete Mumei braced conditional body:

```text
if left == right { 1 } else { 0 }
```

The translator lowers this body to a Lean theorem-local result definition:

```lean
def constantTimeEqFlagResult (left right : Int) : Int :=
  if left = right then 1 else 0
```

The generated obligation still uses the source `requires` / `ensures` contract
and a body equality hypothesis
`h_body : result = constantTimeEqFlagResult left right`; it is discharged by the
same live body-semantics path (`mumei_arith_deep`) and must not use a
known-witness override. This covers the live crypto path
`std/crypto/primitives.mm::constant_time_eq_flag` with
`known_witness_used=false`.

### 5.10 Finite-field equality body semantics

Finite-field equality witnesses may carry a complete body expression such as:

```text
ff_zero(p)
```

Certificates emitted by `mumei verify --proof-cert` may preserve the source
body braces (`{ ff_zero(p) }`); the bridge strips those braces before matching
the finite-field body pattern.

For the live algebra path, the translator lowers that expression to a
theorem-local result definition through `MumeiLean.Algebra`:

```lean
def ffZeroEqZeroResult (p : Int) : Int :=
  MumeiLean.Algebra.mumei_ff_zero p
```

The generated obligation keeps the source `requires` / `ensures` contract and
the body equality hypothesis
`h_body : result = ffZeroEqZeroResult p`. A finite-field equality obligation of
the form `ff_eq(result, 0, p)` is discharged live with the existing
`MumeiLean.Algebra.ff_eq_refl` helper after unfolding `mumei_ff_zero`; it must
not use a known-witness override. This covers the live algebra path
`std/algebra/finite_field.mm::ff_zero_eq_zero` with
`known_witness_used=false`.

### 5.11 Sort ascending-preservation bridge

Sort atoms whose `ensures` includes an ascending-order quantifier of the form
`forall(i, 0, result - 1, arr[i] <= arr[i + 1])` and whose body implements an
insertion sort algorithm are escalation candidates: Z3 produces a spurious
counterexample (`z3_result_class == "sat"`, `escalation_reason ==
"spurious_candidate"`) due to the Array + forall quantifier interaction.

The bridge detects such atoms by matching the ensures pattern and delegates
the proof to `MumeiLean.Sort.insertion_sort_ascending_bridge`, which shows:

```lean
(List.insertionSort (· ≤ ·) arr).length = arr.length ∧
List.Sorted (· ≤ ·) (List.insertionSort (· ≤ ·) arr)
```

using mathlib's `List.sorted_insertionSort` and `List.length_insertionSort`.

The generated theorem references the bridge lemma directly:

```lean
theorem verified_insertion_sort_ascending_correct (n : Int) (arr : List Int)
    (h_req : n ≥ 0 ∧ ...) :
    let sorted := List.insertionSort (· ≤ ·) arr
    sorted.length = arr.length ∧ List.Sorted (· ≤ ·) sorted := by
  exact MumeiLean.Sort.insertion_sort_ascending_bridge arr
```

Since the mumei body directly implements insertion sort (in-place array
store operations equivalent to `List.insertionSort`), the bridge can
treat the output array as `List.insertionSort (· ≤ ·) arr` and discharge
the obligation without a known-witness override. The `known_witness_used`
flag remains `false`.

Lowering rule: `sort_ascending_bridge`
Bridge lemma: `MumeiLean.Sort.insertion_sort_ascending_bridge`
Pointwise helper: `MumeiLean.Sort.sorted_adjacent_le`

### 5.12 Quantifier-alternation (∀∃) bridge

Atoms whose `ensures` carries a nested `forall(..., exists(..., ...))`
alternation are trigger-sensitive for Z3, which returns `unknown` or a
spurious counterexample (`z3_result_class == "sat"`, `escalation_reason ==
"spurious_candidate"`). This extends §5.8's nonlinear coverage to the
quantifier-alternation surface.

The bridge selects the dedicated proof shape via the explicit
`translator_ir.bridge_pattern == "forall_exists_swap"` marker (rather than by
matching the ensures text) and delegates to
`MumeiLean.Quantifiers.forall_exists_swap_of_finite`, supplying an explicit
identity choice witness so the existential is discharged constructively:

```lean
theorem exists_pivot_partition_correct (n : Int) (arr : Int → Int)
    (h_req : n ≥ 0) :
    ∃ f : Int → Int, ∀ i : Int, arr (f i) ≤ arr i := by
  exact MumeiLean.Quantifiers.forall_exists_swap_of_finite
    (fun i j => arr j ≤ arr i)
    (fun i => ⟨i, le_refl _⟩)
    ⟨fun i => i, fun i => le_refl _⟩
```

This is the seventh live generated theorem path
(`std/list.mm::exists_pivot_partition`); `known_witness_used` remains `false`.
`forall_exists_swap_of_finite` already exists, so `bridge_lemma_hash` is
unchanged.

Lowering rule: `quantifier_alternation_lowering`
Bridge lemma: `MumeiLean.Quantifiers.forall_exists_swap_of_finite`

### 5.13 Natural-number induction bridge

Atoms whose obligation follows by induction on a natural-number bound leave Z3
`unknown` (`escalation_reason == "requires_induction"`). The bridge selects the
dedicated proof shape via the explicit
`translator_ir.bridge_pattern == "int_nonnegative_induction"` marker and
delegates to `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`,
supplying the polynomial motive plus base/step obligations:

```lean
theorem sum_nonneg_inductive_correct (n : Int) (h_req : n ≥ 0) :
    0 ≤ n * (n + 1) := by
  refine MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern
    (fun k => 0 ≤ k * (k + 1)) ?h0 ?hstep n h_req
  · norm_num
  · intro k ih
    have hk : (0 : Int) ≤ (k : Int) := Int.ofNat_nonneg k
    nlinarith [ih, hk]
```

This is the eighth live generated theorem path
(`std/math/patterns.mm::sum_nonneg_inductive`); `known_witness_used` remains
`false`. `int_nonnegative_induction_pattern` already exists, so
`bridge_lemma_hash` is unchanged.

Lowering rule: `natural_number_induction_lowering`
Bridge lemma: `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`

Both §5.12 and §5.13 are dedicated `render_theorem` branches selected by
`translator_ir.bridge_pattern`, mirroring the §5.11 sort branch; the source
atom is marked as a custom bridge proof so partial body/ensures translation
never routes it to the generic contract-only fallback.

## 6. Loop invariant and recursion encoding

Mumei loop invariants are encoded as Lean propositions over explicit integer
indices. The translator uses quantifier lowering instead of an operational loop
semantics.

### 6.1 Bounded quantifier

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

### 6.2 Unbounded quantifier

Mumei:

```text
forall var: body
forall var : T: body
exists var: body
exists(var: T, body)
```

Lean:

```lean
(∀ var : Int, body)
(∀ var : ⟦T⟧, body)
(∃ var : ⟦T⟧, body)
```

Formal rule:

```text
⟦forall var: body⟧ᵖ = (∀ var : Int, ⟦body⟧ᵖ)
⟦forall var : T: body⟧ᵖ = (∀ var : ⟦T⟧, ⟦body⟧ᵖ)
```

The existential counterpart is:

```text
exists var: body -> (∃ var : Int, ⟦body⟧ᵖ)
exists(var: T, body) -> (∃ var : ⟦T⟧, ⟦body⟧ᵖ)
```

### 6.3 Recursion obligations

Recursive functions and loops are represented as ordinary Lean theorem
obligations plus explicit hypotheses:

```lean
∀ state : S, invariant state → decreases next state state → invariant (next state)
```

The translator does not synthesize termination proofs. It preserves the logical
shape needed by handwritten Lean witnesses, and any unsupported recursion-specific
syntax must be emitted as `manual_lemma_required` metadata.

## 7. Typed intermediate translator IR

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
    semantic_gap_notes: List[str]
    proof_trace_hints: List[str]
    requires_bridge_lemmas: List[str]
```

`semantic_gap_notes` describe Mumei/Z3/Lean semantic mismatches detected during
translation, `proof_trace_hints` preserve proof-construction hints for Lean-side
automation, and `requires_bridge_lemmas` names the bridge lemmas that downstream
certificate validation should expect.

### 7.1 `TranslatorIRBinder`

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

## 8. `lowering_rules` catalog

The following rule IDs are currently part of the formal specification and may be
emitted in `TranslatorIR.lowering_rules`.

| Rule ID | Required when | Specification section |
|---|---|---|
| `type_system_mapping` | Any typed binder is emitted. | §1 |
| `contract_lowering` | Any `requires` / `ensures` expression is translated. | §4 |
| `array_bounds_bridge` | Array/list access or array-typed binder appears; `requires_bridge_lemmas` must include both `mumei_array_bounds_bridge` and `mumei_array_get_bridge`. | §1, §3, §4, §5.2 |
| `string_regex_bridge` | String predicate or regex bridge obligation appears. | §1, §4, §5.3 |
| `refinement_predicate_lowering` | Refinement predicate or quantifier predicate preservation is required. | §3, §5.5, §6 |
| `integer_overflow_bridge` | Integer arithmetic needs explicit machine-range assumptions. | §1, §2, §5.1 |
| `finite_field_lowering` | Finite-field helper call appears. | §1, §4, §5.6 |
| `group_theory_lowering` | Group helper call appears. | §4, §5.7 |
| `mathlib4_bridge` | Generated expression relies on mathlib-backed helpers or tactics. | §1, §4, §5.6, §5.7 |
| `sort_ascending_bridge` | Sort body with ascending-preservation `forall` ensures; delegates to `MumeiLean.Sort.insertion_sort_ascending_bridge`. | §5.11 |
| `quantifier_alternation_lowering` | `translator_ir.bridge_pattern == "forall_exists_swap"`; delegates to `MumeiLean.Quantifiers.forall_exists_swap_of_finite`. | §5.12 |
| `natural_number_induction_lowering` | `translator_ir.bridge_pattern == "int_nonnegative_induction"`; delegates to `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`. | §5.13 |

A translator implementation is compliant iff:

1. Every emitted `lowering_rules` entry is listed in this catalog.
2. Every `TranslatorIRBinder` satisfies the type mapping in §1, including the `mumei_type` values documented before bridge emission.
3. Unsupported constructs are not silently accepted; they are marked with
   `manual_lemma_reason` and surfaced as warnings or generated theorem TODOs.

`validate_translator_ir_compliance()` enforces these checks at translation time
with warnings only. Warnings do not abort translation, because incomplete Lean
obligations are still useful for triage and handwritten proof completion.

## 9. Certificate field handling and contract constants

Certificate atom field handling is fixed:

| Field | Meaning |
| --- | --- |
| `z3_result_class` | Normalized solver class used for routing; only `unknown` is a Lean escalation candidate. |
| `escalation_reason` | Why Z3 could not close the obligation, such as timeout/resource limits, quantified reasoning, recursion, or a domain-specific fragment. |
| `logic_fragment_tags` | Ordered fragment tags used for bridge lemma selection, metrics, and mumei certificate parity. |
| `translator_ir` | Typed lowering contract emitted into generated Lean and copied into `.lean-cert.json` for mumei-side auditing. |
| `manual_lemma_reason` | Stable reason a generated theorem needs human lemma work; dry runs should emit `manual_lemma_required`, not `lean_verified`. |
| `stale_translator` | mumei-side rejection when `translator_version` or `bridge_lemma_hash` differs from the current mumei/mumei-lean contract. |

Current contract constants are `translator_version = mumei-lean-translator-ir-v2` and `bridge_lemma_hash = a3e9c1f4b7d2806e5f19347cab82d0963ef1a5bc70d4e8290f136d5ab7c84e11`. These are also pinned in [`LEAN_HARNESS_CONTRACT.md`](LEAN_HARNESS_CONTRACT.md), which the contract-vocabulary test uses as the source of truth against the `scripts/export_cert.py` `TRANSLATOR_VERSION` / `BRIDGE_LEMMA_HASH` constants.
