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
| `len(x)` | `mumei_len ⟦x⟧` (`⟦x⟧` scalar), or `((⟦x⟧.length : Int))` when `x` is an array-typed identifier — see §4.8 |
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

### 4.1 Built-in helper names as binders

A helper name from the table above (`max`, `len`, `sum`, `count`, `hash`, …)
that occurs in a contract **only as a bare identifier** — never followed by
`(` — denotes an ordinary scalar variable, not the helper. It lowers to an
`Int` binder with the same name (`lean_binder_name` keeps the spelling, in
lockstep with mumei-core) and the local binder shadows the Lean/mumei helper.
The rule is `builtin_name_binder_lowering` (§8).

```text
top >= 0 && max > 0 && top < max   ->  top ≥ 0 ∧ max > 0 ∧ top < max
                                        binders: (top max : Int)
```

Soundness guard: `render_theorem` binds `requires` / `ensures` / body under one
parameter list, so a name may not be both an `Int` binder and a helper call in
the same theorem. If `max` is bare in one component and `max(a, b)` is called
in another (or bare and called inside a single expression), every affected
translation stays `partial` with `builtin_name_binder_conflict:<name>` in
`unsupported_reasons`; it is never emitted as a buildable theorem. The names
`old`, `holds`, `implies`, `unknown`, `unknown_obligation` are excluded from
the lowering because they carry translator semantics of their own.

Scope: a quantifier / `let` binder spelled like a helper (`forall(max, …)`,
`let max = … in …`) is local to its own scope and is neither bare nor called.
The check is lexical — the same spelling used free *outside* that scope still
counts as a bare occurrence (`forall(max, 0, n, max >= 0) && max >= 0` binds
`max`), so a nested binder never hides a conflict.

Certificate IR: when a certificate ships its own `translator_ir` binder for a
name the current translation lowers under this rule, `ingest_cert` normalises
that binder to `mumei_type = "i64"` / `lean_type = "Int"` and does not add a
second binder for the same name. The rule admits no other type.

### 4.2 Single-expression body blocks

A mumei atom body is a block. When the block consists of exactly one
expression, `translate_body` unwraps the outer braces and translates the inner
expression (`{ top + 1 }` → `top + 1`, `{ if top == max { 1 } else { 0 } }` →
`if top = max then 1 else 0`). Blocks containing statements (`;`, `let … ;`)
or whose outer braces do not enclose the whole source are left to the
existing partial path. A trailing statement carries no `;`, so statement
keywords (`while`, `loop`, `for`, `return`, `break`, `continue`, `mut`, `fn`)
are rejected by keyword: `{ while n > 0 { n } }` is partial with
`statement_block_requires_manual_lemma`. No imperative body is silently
accepted.

Result type: a conditional body takes the common result type of its branches
(`{ if x == 0 { "a" } else { "b" } }` defines a `String`, `{ if p { true }
else { false } }` a `Prop`, list literals a `List Int`, otherwise `Int`). The
type is recorded as `TranslationResult.result_type`. Branches of different
types (`{ if x == 0 { "a" } else { 0 } }`) make the body partial with
`conditional_branch_type_mismatch`; the translator never falls back to `Int`
for a branch it could not type.

### 4.3 Effect-transition statement prefixes in body blocks

A mumei body may run temporal effect transitions before computing its value:

```text
{ perform Vault.check; perform Vault.update; balance - amount }
```

`perform` statements do not produce a value: the block denotes its final
expression. When the whole source is one brace-enclosed block whose top-level
`;`-separated segments are leading `perform <Effect>.<op>` statements
(optionally carrying a call argument list) followed by a single non-empty
tail expression, `translate_body` lowers the tail
(`{ perform Vault.check; balance - amount }` → `balance - amount`). The
ordering obligations of the transitions are carried by the atom's
`effect_pre` / `effect_post` fields and are out of scope for the value
theorem, so the lowering adds no bridge lemma and leaves the obligation
class and `bridge_lemma_hash` unchanged. The rule is
`perform_statement_lowering` (§8).

A block that does not match that shape stays partial: a non-`perform`,
non-`let` statement among the leading segments
(`{ perform A.x; while i < n { i }; y }`), a `perform` statement in tail
position (`{ balance - amount; perform A.x }`), an empty tail, or braces
that do not enclose the whole source. `let` segments in the prefix compose
with `perform` segments via §4.4.
`normalize_body_source` strips the same prefix, so result-type inference
sees the tail (`{ perform Log.append; "ok" }` is a `String` body).

### 4.4 `let` statement sequences in body blocks

A mumei body may bind intermediate names before computing its value:

```text
{ let n = len(buf); let owned = buf; n }
```

Each `let <name> = <expr>` segment binds `<name>` for the rest of the
block; the block denotes its final expression. `translate_body` lowers the
tail with every binding substituted textually — `<name>` occurrences in
later segment expressions and in the tail are replaced by their bound
expression, parenthesized when it is compound
(`{ let owned = buf; len(owned) }` → `len(buf)` → `(mumei_len buf)`).
Bindings resolve sequentially, so a later binding may reference earlier
names (`{ let x = a; let x = x + 1; x }` → `(a + 1)`) and `perform`/`let`
segments may interleave (both rules are recorded, §4.3). Substitution is
an equational rewriting of a pure expression, so the lowering adds no
bridge lemma and leaves `bridge_lemma_hash` unchanged. The rule is
`let_statement_lowering` (§8).

Substitution stays conservative — the block remains partial when:

- a bound name is rebound inside the tail (`let` / `forall` / `exists`
  binder), e.g. `{ let n = len(buf); forall(n, 0, m, arr[n] >= 0) }`;
- a bound name appears in call position in the tail
  (`{ let f = len; f(buf) }`);
- the block ends in a `let`/`perform` statement or any segment is neither
  `let` nor `perform`;
- `==` is used instead of `=` (`{ let owned == buf; owned }`).

`normalize_body_source` applies the same lowering, so result-type
inference sees the substituted tail (`{ let msg = "ok"; msg }` is a
`String` body).

### 4.5 Nested conditionals in `if { } else { }` bodies

A mumei body may nest conditionals inside either branch:

```text
{ if x < lo { lo } else { if x > hi { hi } else { x } } }
```

`_parse_braced_if` splits a brace-delimited conditional by brace depth
instead of a flat regex, so branch bodies may contain their own `{ … }`
blocks — nested `if`, `else if` chains (`else if c { b } else { d }` is
taken verbatim as the else source), or any block form §4.1–§4.4 lowers.
Each branch recurses through `translate_body`, and the merged result is
the Lean `if … then … else …` term
(`{ if x < lo { lo } else { if x > hi { hi } else { x } }` →
`if x < lo then lo else if x > hi then hi else x`). The lowering is a
syntactic embedding of mumei's conditional semantics, adds no bridge
lemma, and leaves `bridge_lemma_hash` unchanged. The rule is
`nested_if_lowering` (§8), recorded only when a branch actually carried
braces — flat `if c { a } else { b }` bodies keep their prior rule set.

Malformed shapes stay partial: trailing tokens after the else block,
`else ifx` (not a chain), a missing `else`, an empty condition
(`if { a } else { b }`), or a nested `if` without its own `else`. Generated theorems for nested-if bodies are discharged by
`mumei_arith_deep`, whose `split <;> omega` stage splits the `if` goals
without a new ladder candidate.

### 4.6 Struct field projection (`p.x`)

A mumei atom may read a field of a struct-typed parameter:

```text
atom take_point(p: Point)
requires: p.x >= 0;
ensures: result >= 0;
body: p.x;
```

Struct fields are opaque to the prover — the certificate carries no field
types or layout, only the param binder `p : Point`. The translator lowers
each `base . field` token triple to a fresh scalar binder `base_field`
(`p.x` → `p_x : Int`) identically in `requires`, `ensures`, and `body`,
so the generated theorem quantifies the projected value directly
(`takePointResult (p_x : Int) : Int := p_x`). The lowering is a
consistent opaque renaming, adds no bridge lemma, and leaves
`bridge_lemma_hash` unchanged. The rule is `struct_projection_lowering`
(§8), recorded whenever at least one `base . field` rewrite was applied.

Shapes that are not plain field reads stay partial: qualified effect
names (`perform Eff.op`), method calls (`p.f(…)`), postfix access on a
call result (`f(p).x`), non-identifier members (`p.5`), and projected
names that would collide with an existing binder (`p.x` next to a real
`p_x` would conflate two distinct values — the raw `.` keeps the surface
partial instead of silently equating them). Chained access `p.x.y`
lowers to a single `p_x_y` binder.

### 4.7 Structured-concurrency bodies (`task`, `task_group:all`)

A mumei body may spawn structured tasks:

```text
body: {
    task_group:all {
        task { a };
        task { b }
    }
};
```

A bare `task { e }` evaluates to its body `e`. A `task_group:all` runs
every child task to completion and yields the *last* task's value, so the
block lowers to the last task's translated body
(`{ task_group:all { task { a }; task { b } } }` → `b`). Sibling tasks'
effects are ordering obligations — carried by the atom's effect metadata,
not part of the group value — mirroring how §4.3 `perform` statements are
dropped. Every task item must be a `task { … }` block and every task body
must itself translate cleanly; otherwise the block stays partial. Task
bodies recurse through `translate_body`, so §4.1–§4.6 forms compose
inside them (e.g. `task { let acc = n; acc = acc + 2; acc }` lowers via
the let-sequence machinery — which also accepts `<name> = <expr>` rebind
segments on `let`-bound names, recorded as `rebind_statement_lowering`).

`task_group:any { task { e₁ }; …; task { eₙ } }` yields whichever task
finishes first — modelled as list membership over the candidate values.
The block lowers to the list literal `[e₁, …, eₙ]` with
`result_type = "List Int"`, so `render_theorem` emits
`def <atom>Result … : List Int` and hypothesises
`h_body : result ∈ <atom>Result …` (the observed `result` binder stays
`Int` — the list type feeds only the `def`). The generated proof runs
`fin_cases h_body <;> <tactic>`, which splits the membership into one
goal per candidate value (`result := eᵢ` substituted) and closes each
with the arithmetic cascade under `requires`. Every task body must
lower cleanly *and* be `Int`-typed — a Prop- or String-valued element
would make the membership hypothesis ill-typed, so such groups stay
partial (still tagged `concurrency_obligation` for triage, without the
lowering rule).

`task` and `task_group` are also statement keywords: a `task` surface
that does not occupy the whole body (trailing text such as
`task { a } + x`, an empty `task { }`, or a task nested in a `let` RHS
like `let x = task { 5 }; x`) cannot leak raw mumei braces into the
emitted Lean — the residual token flags `statement_block_requires_manual_lemma`
and the body stays partial.

The same treatment covers every other reserved concurrency/ownership
token with no lowering — `async`, `await`, `cancel`, `send`, `recv`,
`chan`, `acquire`, `consume`, `exclusive`, `shared`, `ref`, `as`,
`invariant`, `decreases` — plus the channel send/recv arrow: `ch <- v`
and `<- ch` tokenise as separate `<` / `-` ops and would otherwise be
reinterpreted as the comparison `ch < -v`, so a raw-source guard flags
`channel_arrow_requires_manual_lemma` (the `->` arrow is guarded the
same way). Extra enclosing braces around an already-lowered
`task`/`task_group` body are transparent, matching the `perform`/`let`
statement-sequence rule.

`obligation_class` is producer-declared metadata: mumei-emitted
certificates do not carry it (the field exists only in `translator_ir`
payloads written by tooling that knows the class), so `obligation_class_of`
falls back to `logic_fragment_tag` for tactic-history keys on real certs.
Body-derived classes are therefore *not* merged back into stored IR on
ingest — doing so would silently change every pre-existing atom's
learning key.

The lowering introduces the `concurrency_obligation` obligation class
(§10) whose bridge lemmas (`MumeiLean.Concurrency.task_group_all_result_last`,
`task_group_any_result_mem`, `task_value_result`) pin the task-value
semantics in the trusted kernel — this catalog addition bumps
`bridge_lemma_hash`. Recorded rules are `task_value_lowering`,
`task_group_all_lowering`, and `task_group_any_lowering` (partial `any`).

### 4.8 While-loop invariant bodies (verification-condition emission)

A body of the shape

```text
{ let-init*; while <cond> invariant: <I> [decreases: <D>] { <assigns> }; <tail> }
```

lowers to the loop's verification conditions instead of a value term. The
translator collects the loop-carried variables (the names assigned inside the
loop body — every body statement must be a scalar rebind `x = e`), resolves the
pre-loop `let` initialisers, and records the pieces on
`TranslationResult.loop_vc` (`LoopVCPieces`): the invariant `I`, its
entry-specialisation `I[init]`, the post-iteration image `I[σ']` where `σ'`
substitutes every carried name by its body RHS **simultaneously** (so the
`i ↦ i + 1` image cannot rewrite inside the `sum ↦ sum + arr[i]` image), the
loop condition, the (optional) `decreases` measure and its post image, and the
tail expression.

`render_theorem` then emits no `def`/`h_body` at all — the theorem goal itself
is the VC conjunction, with the carried variables universally quantified
inside the conjuncts and `result` bound inside the post conjunct (so neither
becomes a theorem parameter):

```text
theorem <atom>_correct (<params>) :
    (⟦requires⟧) →
      (I[init]) ∧
      (∀ <carried> : Int, (I ∧ c) → I[σ']) ∧
      (∀ <carried> : Int, (I ∧ c) → (0 ≤ D ∧ D[σ'] < D)) ∧   -- absent without decreases
      (∀ <carried> : Int, (I ∧ ¬ c) → ∀ (result : T), result = ⟦tail⟧ → ⟦ensures⟧)
```

where `T` is the atom's declared return type: the `role: "result"`
binder's `lean_type` (or its `mumei_type` mapped via
`declared_lean_type` — `[t]`/`array<t>` → `List t`, scalars via
`_FORMAL_SPEC_TYPE_MAPPINGS`), falling back to the usage-scan
partitions and then `Int`.

This mirrors the mumei verifier's own loop checks (invariant at entry,
preserved per iteration, measure descending, exit state discharges
`ensures`). Requiring the invariant inside each conjunct — rather than
treating `I ∧ ¬ c` as a proved hypothesis — keeps the statement sound: if the
invariant does not actually hold the theorem is simply unprovable, never
falsely verified. Recorded rule: `while_loop_invariant_lowering`.

Conservative partials: a `while` that is not the second-to-last segment, a
loop without `invariant:`, a body containing anything but scalar rebinds
(nested loops, array-element writes, `perform`), a missing tail, or any
partial piece leaves the body partial (no rule recorded). A loop-carried name
initialised only by an outer parameter (no `let`) keeps its incoming value as
the base substitution **and stays a theorem parameter** — the conjuncts still
∀-bind the loop's own name, but the base conjunct reads on the parameter. Only
`let`-initialised carried vars are removed from the signature; dropping an
externally bound carried name would leave the base conjunct referencing an
unbound identifier (ill-typed Lean). The theorem signature itself is built
from the certificate's `translator_ir` binders minus `role: result` — see
below for declared-type authority. The post conjunct ∀-binds `result` at
the declared return type, so a while loop returning `[t]` emits
`len(result)`/`result[i]` forms that elaborate as `List` operations; when
the certificate declares no result type the usage-scan partitions
(`result` indexed → `List Int`, passed to string predicates → `String`)
and finally the scalar `Int` default apply — a mistyped binder can only
fail elaboration, never fabricate a proof.

**`len(arr)` on arrays.** When an identifier appears both in `arr[i]` /
`sum(arr, …)` position (i.e. it will be bound as `List Int`) and as the
argument of `len`, the call lowers to `((arr.length : Int))` — `mumei_len`
takes `Int` and would emit ill-typed Lean. A `len(x)` whose argument is never
indexed keeps the scalar `mumei_len` lowering; `x` then stays an `Int` binder.
Loop pieces share one array-name scan over the whole `{ …; while …; tail }`
source, so `len(arr)` in the condition sees `arr[j]` indexing that only
occurs inside the invariant. At ingest level the scan widens to the whole
atom (`atom_array_names(requires, ensures, body)`): a name indexed in any
clause is `List Int` in the theorem signature, so `len` on it lowers to
`.length` in *every* clause — `result <= len(arr)` in `ensures` would
otherwise emit ill-typed `mumei_len arr` against the `List Int` binder.
Declared types are authoritative over the usage scan: when the
certificate's `translator_ir` binders mark a parameter `[t]`/`array<t>`/
`List Int`, ingest unions that name into `atom_array_names` and the theorem
signature, so a list parameter that is never indexed (e.g. only referenced
via `len(x)`) still binds `List Int` and `len(x)` still lowers to
`.length`. For loop-VC theorems the signature likewise comes from the
certificate's `translator_ir` binders (with `role: result` excluded —
`result` is quantified inside the post conjunct), falling back to the
usage-scan partition when the certificate carries no binder table.
Quantifier hypotheses follow the same rule: mumei extracts each
`forall`/`exists` conjunct out of `requires` (rendering it `true`) into
`forall_constraints`, and ingest restores them as `forall(var, lo, hi,
cond)` requires conjuncts before translation — the step VC's elementwise
hypothesis (`arr[i] ≥ 0`) exists only there, so without restoration the
emitted VC is structurally unprovable.

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

Goals stated over the field carrier itself (rather than over closure bounds) are
discharged by the `mumei_field` tactic cascade: `ring1`, then a `simp only` over
the `MumeiLean.Algebra` carrier definitions followed by `ring_nf`, then `group`,
`field_simp`, `ring_nf`, `omega`, and finally `simp`. `mumei_arith` and
`mumei_arith_deep` additionally try `ring1` and `field_simp` so crypto and
finite-field obligations reaching the generic body-semantics path are closed
without a manual lemma. The cascade uses `ring1` rather than `ring` because
mathlib's `ring` succeeds after normalising an unclosed goal, which would
swallow the remaining stages.

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
supplying the polynomial motive plus base/step obligations. The emitted goal is
the **universally quantified** statement `∀ k : Int, 0 ≤ k → 0 ≤ k * (k + 1)`,
which matches the atom's `forall(k, 0, n, k * (k + 1) >= 0)` ensures — proving
only the single instance `0 ≤ n * (n + 1)` at the bound would be strictly weaker
than the contract, so the theorem statement is the universal that entails it:

```lean
theorem sum_nonneg_inductive_correct (n : Int) (h_req : n ≥ 0) :
    ∀ k : Int, 0 ≤ k → 0 ≤ k * (k + 1) := by
  refine MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern
    (fun k => 0 ≤ k * (k + 1)) ?h0 ?hstep
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

### 5.14 Finite-field commutativity bridge

An atom whose body is a single commutative finite-field helper call and whose
`ensures` compares the result to the same call with swapped operands, e.g.

```text
body_expr: { ff_mul(a, b, p) }
ensures:   ff_eq(result, ff_mul(b, a, p), p)
```

is a Lean escalation candidate: the operands are equal only modulo `p`, so Z3
reports `unknown` on the nonlinear `%` interaction. The translator lowers the
braced body through the finite-field helpers, exactly as for a bare call:

```lean
def ffMulCommutativeResult (p b a : Int) : Int :=
  (MumeiLean.Algebra.mumei_ff_mul a b p)
```

and the generated theorem is discharged by the matching commutativity bridge
lemma:

```lean
theorem ff_mul_commutative_correct (p b a : Int) (result : Int)
    (h_body : result = ffMulCommutativeResult p b a) :
    (p > 0) → ((MumeiLean.Algebra.mumei_ff_eq result
        (MumeiLean.Algebra.mumei_ff_mul b a p) p)) := by
  rw [h_body]
  unfold ffMulCommutativeResult
  intro _hp
  exact MumeiLean.Algebra.ff_mul_comm_eq a b p
```

`ff_add` is handled identically through `MumeiLean.Algebra.ff_add_comm_eq`. This
is the tenth live generated theorem path
(`std/algebra/finite_field.mm::ff_mul_commutative`) and keeps
`known_witness_used = false`. Both bridge lemmas are new catalog entries (§10),
so this path bumps `bridge_lemma_hash`.

Lowering rule: `finite_field_commutativity_lowering`
Bridge lemmas: `MumeiLean.Algebra.ff_add_comm_eq`,
`MumeiLean.Algebra.ff_mul_comm_eq`

### 5.15 Finite-field associativity bridge

An atom whose body left-associates a finite-field helper call and whose
`ensures` compares the result to the right-associated call, e.g.

```text
body_expr: { ff_mul(ff_mul(a, b, p), c, p) }
ensures:   ff_eq(result, ff_mul(a, ff_mul(b, c, p), p), p)
```

is a Lean escalation candidate for the same reason as §5.14: the two nestings
agree only after the intermediate `%` reductions are pushed through the product,
so Z3 reports `unknown`. The path is selected by the explicit
`translator_ir.bridge_pattern == "finite_field_associativity"` marker (as in
§5.12 / §5.13) rather than by name matching, and the body is lowered through the
finite-field helpers:

```lean
def ffMulAssociativeResult (p a b c : Int) : Int :=
  (MumeiLean.Algebra.mumei_ff_mul (MumeiLean.Algebra.mumei_ff_mul a b p) c p)
```

The generated theorem re-associates with the matching `*_assoc_mod` bridge
lemma and closes by `ff_eq` reflexivity:

```lean
theorem ff_mul_associative_correct (p a b c : Int) (result : Int)
    (h_body : result = ffMulAssociativeResult p a b c) :
    (p > 0) → ((MumeiLean.Algebra.mumei_ff_eq result
        (MumeiLean.Algebra.mumei_ff_mul a
          (MumeiLean.Algebra.mumei_ff_mul b c p) p) p)) := by
  rw [h_body]
  unfold ffMulAssociativeResult
  intro _hp
  rw [MumeiLean.Algebra.ff_mul_assoc_mod]
  exact MumeiLean.Algebra.ff_eq_refl _ p
```

`ff_add` is handled identically through `MumeiLean.Algebra.ff_add_assoc_mod`.
This is the eleventh live generated theorem path
(`std/algebra/finite_field.mm::ff_mul_associative`) and keeps
`known_witness_used = false`. Both backing lemmas already exist in the catalog
(§10), so this path leaves `bridge_lemma_hash` unchanged. An `ensures` whose
operand order is not the re-association of the body (for example
`ff_eq(result, ff_mul(b, ff_mul(a, c, p), p), p)`) does not match and falls back
to the generic `mumei_arith_deep` body-semantics tactic.

Lowering rule: `finite_field_associativity_lowering`
Bridge lemmas: `MumeiLean.Algebra.ff_add_assoc_mod`,
`MumeiLean.Algebra.ff_mul_assoc_mod`, `MumeiLean.Algebra.ff_eq_refl`

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
| `finite_field_commutativity_lowering` | `ff_eq` appears together with `ff_add` / `ff_mul`; `requires_bridge_lemmas` must include `MumeiLean.Algebra.ff_add_comm_eq` and `MumeiLean.Algebra.ff_mul_comm_eq`. | §5.6, §5.14 |
| `group_theory_lowering` | Group helper call appears. | §4, §5.7 |
| `mathlib4_bridge` | Generated expression relies on mathlib-backed helpers or tactics. | §1, §4, §5.6, §5.7 |
| `sort_ascending_bridge` | Sort body with ascending-preservation `forall` ensures; delegates to `MumeiLean.Sort.insertion_sort_ascending_bridge`. | §5.11 |
| `quantifier_alternation_lowering` | `translator_ir.bridge_pattern == "forall_exists_swap"`; delegates to `MumeiLean.Quantifiers.forall_exists_swap_of_finite`. | §5.12 |
| `natural_number_induction_lowering` | `translator_ir.bridge_pattern == "int_nonnegative_induction"`; delegates to `MumeiLean.AdvancedPatterns.int_nonnegative_induction_pattern`. | §5.13 |
| `builtin_name_binder_lowering` | A built-in helper name appears only as a bare identifier and is bound as an `Int` theorem parameter; no bridge lemma is required. | §4.1 |
| `perform_statement_lowering` | A body block is a sequence of leading `perform <Effect>.<op>` statements followed by a pure tail; only the tail lowers and no bridge lemma is required. | §4.3 |
| `let_statement_lowering` | A body block's leading `let <name> = <expr>` statements substitute into the final tail expression; the substituted tail lowers and no bridge lemma is required. | §4.4 |
| `nested_if_lowering` | A braced `if c { a } else { b }` body carries brace-enclosed content (a nested conditional or block) in a branch; each branch recurses through the translator and no bridge lemma is required. | §4.5 |
| `struct_projection_lowering` | A `base . field` member access appears; the field read becomes a scalar `base_field` binder consistently across `requires` / `ensures` / `body` and no bridge lemma is required. Qualified effect names (`perform Eff.op`), method calls (`p.f(…)`), postfix access on call results, non-identifier members, and colliding projected names stay partial. | §4.6 |
| `rebind_statement_lowering` | A `x = e` statement rebinds a `let`-bound name inside a statement sequence; the new expression substitutes like a `let` binding and no bridge lemma is required. Parameter reassignment stays partial. | §4.4, §4.7 |
| `task_value_lowering` | A bare `task { e }` body lowers to `e`; tags the `concurrency_obligation` class. | §4.7 |
| `task_group_all_lowering` | A `task_group:all { task {…}; … }` body lowers to its last task's value; tags the `concurrency_obligation` class. | §4.7 |
| `task_group_any_lowering` | A `task_group:any { task {…}; … }` body lowers to the candidate-value `List Int`; the theorem hypothesises `result ∈ <def>` and `fin_cases` splits membership; tags the `concurrency_obligation` class. | §4.7 |
| `while_loop_invariant_lowering` | A `{ let-init*; while c invariant: I [decreases: D] { assigns }; tail }` body lowers to the loop's verification conditions; the theorem goal is `requires → I[init] ∧ (∀ carried, I ∧ c → I[σ']) ∧ (∀ carried, I ∧ c → 0 ≤ D ∧ D[σ'] < D) ∧ (∀ carried, I ∧ ¬c → result = tail → ensures)` with no `def`/`h_body` emitted. | §4.8 |

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

Current contract constants are `translator_version = mumei-lean-translator-ir-v2` and `bridge_lemma_hash = 5716cfdd945d68b4a0d75d75c5ade1934cbd76e0dfe16734a8f3dd723cfdd8e9`. These are also pinned in [`LEAN_HARNESS_CONTRACT.md`](LEAN_HARNESS_CONTRACT.md). `tests/test_contract_vocabulary.py` anchors both the constant-defining scripts (`scripts/export_cert.py`, `scripts/expr_translator.py`) and every pinned doc (this file, `LEAN_HARNESS_CONTRACT.md`, `BRIDGE_HARNESS_SPEC.md`, `INTEGRATION.md`) to the same expected literals, so any bump must update all of them in a single diff.

`bridge_lemma_hash` is derived from the obligation-class bridge lemma catalog
(§10) by `expr_translator.compute_bridge_lemma_hash()`: the canonical pre-image
is one `<obligation_class>:<lemma>` line per catalog entry, sorted by class and
then by lemma, hashed with SHA-256. Adding, renaming, or removing a backing
lemma therefore changes the constant, and certificates produced by the previous
catalog are `stale_translator` rather than silently reusable. Consumers that
mint certificates with this contract — currently mumei-agent's Solidity
guard-trace path (`_SOLIDITY_GUARD_TRACE_BRIDGE_LEMMA_HASH`) — must be bumped in
lockstep.

## 10. Obligation class bridge lemma catalog

Every escalated atom is classified by `classify_obligation()` into exactly one
obligation class, and `obligation_bridge_lemmas()` maps the class to the Lean
entry points that may discharge it. The nine base classes below are the
documented taxonomy; the three `smart_contract_*` trace classes
(`smart_contract_guard_trace_obligation`,
`smart_contract_access_control_obligation`, `smart_contract_cei_obligation`)
extend it for Solidity trace obligations and route to `MumeiLean.SmartContract`.

| Obligation class | Lean modules | Bridge lemma entry points |
|---|---|---|
| `quantifier_obligation` | `MumeiLean.Quantifiers`, `MumeiLean.AdvancedPatterns` | `skolemize_exists`, `herbrand_forall`, `bounded_forall_of_unrestricted`, `bounded_exists_of_witness`, `forall_and_intro`, `nested_forall_intro`, `nested_exists_intro`, `forall_exists_swap_of_finite`, `bounded_forall_split_at`, `bounded_forall_shift`, `bounded_exists_of_nonempty_forall`, `bounded_forall_weaken`, `bounded_exists_map`, `nested_forall_swap`, `int_nonnegative_induction_pattern`, `bounded_forall_imp`, `bounded_forall_of_field_range`, `nested_bounded_forall_intro` |
| `finite_field_obligation` | `MumeiLean.Algebra`, `MumeiLean.AdvancedPatterns` | `ff_add_in_field`, `ff_mul_in_field`, `ff_sub_in_field`, `ff_neg_in_field`, `ff_zero_in_field`, `ff_one_in_field`, `ff_eq_refl`, `ff_eq_symm`, `ff_eq_trans`, `ff_add_comm`, `ff_mul_comm`, `ff_add_zero`, `ff_mul_one`, `ff_sub_self_eq_zero_mod`, `ff_add_comm_eq`, `ff_mul_comm_eq`, `ff_add_assoc_mod`, `ff_mul_assoc_mod`, `ff_pow_zero`, `ff_inv_zero`, `finite_field_binary_closed`, `finite_field_commutativity_pattern`, `finite_field_obligation_closure` |
| `group_theory_obligation` | `MumeiLean.Algebra`, `MumeiLean.AdvancedPatterns` | `group_mul_assoc`, `group_left_inv`, `group_right_inv`, `group_mul_one`, `group_one_mul`, `group_inv_inv`, `group_mul_inv_rev`, `mumei_group_comm_int`, `group_mul_left_cancel`, `group_pow_zero`, `group_pow_add`, `group_conj_inv`, `mumei_group_pow_zero_int`, `group_conjugation_pattern`, `group_hom_preserves_mul`, `group_theory_obligation_assoc_law` |
| `crypto_primitive_obligation` | `MumeiLean.Crypto`, `MumeiLean.AdvancedPatterns` | `hash_deterministic`, `hash_modulus_bounds`, `encryption_roundtrip`, `rsa_signature_correct`, `signature_verify_sound`, `kdf_deterministic`, `hmac_deterministic`, `commitment_binding_pattern`, `zk_verify_soundness`, `commitment_deterministic`, `commitment_same_inputs`, `zk_verify_stable_under_equal_inputs`, `hash_stability_under_equal_inputs`, `hmac_modulus_bounds`, `commitment_modulus_bounds`, `signature_pattern`, `encryption_pattern`, `crypto_obligation_roundtrip` |
| `arithmetic_obligation` | `MumeiLean.Algebra`, `MumeiLean.AdvancedPatterns` | `sc_subtraction_nonnegative`, `arith_add_upper_bound`, `arith_add_monotone`, `arith_mul_nonneg_of_nonneg`, `arith_square_nonneg`, `arith_bounded_of_interval`, `arithmetic_obligation_bounded_combination`, `arithmetic_obligation_monotone_step` |
| `smart_contract_obligation` | `MumeiLean.AdvancedPatterns` | `sc_withdraw_allowed_intro`, `sc_no_negative_after_withdraw`, `smart_contract_obligation_guard_preserved`, `smart_contract_obligation_balance_preserved` |
| `rtgs_obligation` | `MumeiLean.AdvancedPatterns`, `MumeiLean.Algebra` | `rtgs_balance_conserved_refl`, `rtgs_trace_safe_intro`, `rtgs_obligation_conservation`, `rtgs_obligation_trace_safe`, `rtgs_transfer_conserves_sum`, `rtgs_transfer_conserves_sum_of_amounts`, `rtgs_debit_leaves_nonnegative` |
| `concurrency_obligation` | `MumeiLean.Concurrency` | `task_group_all_result_last`, `task_group_any_result_mem`, `task_value_result` |
| `unknown_obligation` | `MumeiLean.AdvancedPatterns` | `unknown_obligation_intro`, `unknown_obligation_discharged_by_manual_lemma` |

Catalog rules:

1. A lemma may only be listed after it exists in the corresponding Lean module
   and `lake build` proves it without `sorry`.
2. Listing a lemma does not promote an atom by itself; promotion still requires
   a generated theorem that builds (§5) with current contract constants (§9).
3. `unknown_obligation` entries are triage scaffolding: they keep the generated
   theorem traceable while `manual_lemma_reason` stays set.
4. Syntax lowerings that only widen the translated fragment (§4.1, §4.2) do
   not touch this catalog; `bridge_lemma_hash` is unchanged by them and no
   `stale_translator` rejection is triggered.

## 11. Escalation timing

The bridge records how long the Lean escalation took so callers can budget it:

| Field | Location | Meaning |
|---|---|---|
| `lean_solver_time_s` | each atom's `lean_result_metadata` (and `lean_metadata`) | Wall-clock seconds of the `lake build` that decided this atom's status; `null` on dry runs (`--no-build`) and when `lake` is missing. |
| `lean_solver_time_s` | bridge summary JSON under `lean_fallback` | Same measurement at run scope, so scan/bundle runs report one aggregate escalation cost. |

`mumei`'s benchmark runner consumes the same field name in
`benchmarks/run_benchmarks.py` (`details.lean_solver_time_s`) and reports `SKIP`
with zero cost when no Lean escalation candidate exists, so the timing surface
is identical on both sides of the bridge.

The automatic tactic search (§12) runs inside the same escalation window, so the
seconds it consumes are added to the atom's `lean_solver_time_s`; there is no
second timing channel.

## 12. Automatic tactic search for residual obligations

§5 selects a bridge lemma template per obligation class. Atoms no template
matches fall back to the generic `mumei_arith` / `mumei_arith_deep` cascade, and
atoms whose translation records a `manual_lemma_reason` (for example
`unknown_obligation_requires_manual_lemma`) are not emitted at all — they wait
for a hand-written lemma. `scripts/tactic_search.py` closes part of that residue
automatically by *searching* for a tactic that discharges the already-rendered
goal.

### 12.1 Eligibility

An atom is search-eligible iff all of the following hold:

1. Its statement is faithful: neither `requires`, `ensures`, nor the body
   translation is a partial translation (`is_partial`). A partially translated
   statement does not represent the mumei obligation, so no tactic may promote
   it.
2. No custom bridge-proof generator (§5.11–§5.15) already owns the atom.
3. Either a `manual_lemma_reason` is set (stage `residual`), or the atom's
   generated proof failed `lake build` while using only the generic
   `mumei_arith` / `mumei_arith_deep` fallback (stage `build_failure`).

A `manual_lemma_reason` carried by the *certificate* (mumei's own
`manual_lemma_reason` field) is a human-review marker and continues to block
promotion in `scripts/export_cert.py` regardless of the search outcome.

### 12.2 Candidate ladder

The ladder is a fixed, ordered list; the search adopts the first entry that
closes the goal, so the result is deterministic for a given goal and Lean
toolchain:

| # | Candidate id | Tactic |
|---|---|---|
| 1 | `omega` | `omega` |
| 2 | `linarith` | `linarith` |
| 3 | `nlinarith` | `nlinarith` |
| 4 | `positivity` | `positivity` |
| 5 | `norm_num` | `norm_num` |
| 6 | `ring` | `ring1` |
| 7 | `field_simp` | `field_simp` |
| 8 | `decide` | `decide` |
| 9 | `simp_arith` | `simp_all <;> omega` |
| 10 | `mumei_field` | `mumei_field` |
| 11 | `mumei_ff_mod` | `mumei_ff_mod` |
| 12 | `aesop` | `aesop` |
| 13 | `tauto` | `tauto` |
| 14 | `mumei_list` | `mumei_list` |
| 15 | `mumei_order` | `mumei_order` |
| 16 | `mumei_induct` | `mumei_induct` |
| 17 | `mumei_ff_pow` | `mumei_ff_pow` |

Entries 1–12 cover arithmetic, modular and field goals. Entries 13–17 widen the
ladder to the goal classes those tactics leave open, and are appended rather
than interleaved so the adopted tactic for every previously searched goal is
unchanged:

* `tauto` — propositional goals over predicate-parametric contracts
  (`holds(p, x)`, `==>`), including classically-valid shapes such as the
  Peirce-shaped guard collapse that `aesop` does not close. It discharges
  `predicate_guard_collapse`, the thirteenth live generated theorem path.
* `mumei_list` — goals stated through the recursive list helpers
  (`mumei_len`, `mumei_sum`, `mumei_count`). The helpers are opaque to `omega`,
  so the tactic unfolds them together with `List.filter` / `List.length`
  simplification before closing arithmetically.
* `mumei_order` — order goals (`min` / `max` normalisation, transitivity,
  monotonicity of products) whose closing step is an ordering lemma rather than
  a linear-arithmetic decision.
* `mumei_induct` — goals relating a recursive helper to a structural measure,
  which only reduce after an induction on the list (or `Nat`) binder. The
  binder is picked by type, keeping the emitted proof free of generated names.
* `mumei_ff_pow` — finite-field goals containing `mumei_ff_pow`, i.e. modular
  exponentiation. `mumei_ff_mod` normalises products and sums but leaves both
  the `Int.toNat` exponent literal and a reduction sitting under the exponent
  (`(a % p) ^ n % p`) in place; this stage adds `Int.reduceToNat` and
  `MumeiLean.Algebra.emod_pow_emod` so a power term also collapses into a single
  `polynomial % p`. It discharges `ff_pow_square_expands`, the fourteenth live
  generated theorem path.

The five new tactics are defined in `MumeiLean/Tactics.lean` and their goal
shapes are pinned by `tests/fixtures/tactic_ladder_driver.lean`.

`mumei_ff_mod` (`MumeiLean/Tactics.lean`) is the modular-normalisation stage for
finite-field goals stated through the `mumei_ff_*` helpers: it unfolds the
helpers, collapses iterated `%` reductions with
`Int.emod_emod_of_dvd _ (dvd_refl _)`, pushes the remaining `Int.mul_emod` /
`Int.add_emod` rewrites through the product, and closes with `rfl` / `ring_nf` /
`omega`. It is what discharges finite-field distributivity, the twelfth live
generated theorem path (`ff_mul_add_distributive`).

Every candidate is emitted as `(intros; <tactic>)` because generated statements
are `requires → ensures` implications, exactly like the generic `mumei_arith`
cascade it replaces.

Candidates run against the *same rendered theorem* the bridge would emit: the
probe module reuses `render_theorem()` with the candidate substituted for the
fallback tactic, wrapped in a per-candidate namespace, so a probe success and
the final emission agree by construction.

### 12.3 Budget and determinism

All candidates for one obligation are compiled in a single `lake env lean`
invocation bounded by a per-obligation timeout
(`--tactic-search-timeout`, default 300s) and
`set_option maxHeartbeats 400000` per candidate. A candidate counts as
successful only when the probe compile reports neither an error nor a `sorry`
warning inside that candidate's line span. Timeout, missing `lake`, or an
exhausted ladder all leave the atom exactly as it was.

### 12.4 Metadata and soundness

| Field | Meaning |
|---|---|
| `tactic_search.stage` | `residual` or `build_failure`. |
| `tactic_search.adopted_tactic` | Candidate id adopted, or `null`. |
| `tactic_search.candidates_tried` | Ladder entries considered up to and including the adopted one. |
| `tactic_search.search_time_s` | Wall-clock seconds spent probing this obligation. |
| `tactic_search.exhausted` | `true` when no candidate closed the goal. |
| `tactic_search.timed_out` | `true` when the probe compile hit the per-obligation timeout. |
| `tactic_search.history_ranked` | `true` when the learned ranking of §12.5 reordered the ladder for this obligation. |
| `tactic_search.history_fingerprint` | sha256 of the history artifact that produced the ranking, or `null`. |
| `diagnostics[]` | `tactic_search_adopted=<id>` on success, `tactic_search_exhausted` otherwise. |

Soundness rules:

1. An adopted tactic never promotes an atom on its own. The adopted tactic is
   written into the generated module and the atom is promoted only if the real
   `lake build` of that module then succeeds, with current contract constants
   (§9).
2. When no candidate succeeds, `manual_lemma_reason` is preserved verbatim and
   the status stays `manual_lemma_required`; the search never rewrites or drops
   the reason.
3. The search does not add bridge lemmas to the catalog (§10), so it leaves
   `translator_version` and `bridge_lemma_hash` unchanged. Widening the ladder
   (§12.2) and learning a ranking (§12.5) are likewise proof-search changes, not
   contract changes: they cannot make a goal provable that `lake build` rejects.

### 12.5 Learned candidate order

Re-probing candidates that have never closed a goal of the obligation class at
hand is the ladder's main cost. The search therefore *learns* an order from past
runs, under a restriction that keeps §12.3 intact: learning may only permute the
ladder, never extend, shrink or randomise it.

The learned state is a pinned, version-controlled artifact,
`data/tactic_search_history.json` (schema
`mumei-lean.tactic_search_history/v1`):

```json
{
  "schema": "mumei-lean.tactic_search_history/v1",
  "entries": [
    {
      "obligation_class": "finite_field",
      "stage": "build_failure",
      "candidate": "mumei_ff_mod",
      "successes": 1
    }
  ]
}
```

Rules:

1. **Key.** Entries are keyed by `(obligation_class, stage)`. The class is the
   translator IR's `obligation_class`; certificates whose IR predates that field
   fall back to the atom's `logic_fragment_tag`, and otherwise to
   `unclassified`.
2. **Ranking.** For a given key, candidates are sorted by descending recorded
   `successes`; ties — including every candidate with no record — keep the
   declared ladder order of §12.2. The ranking is a permutation of the ladder,
   so a recorded candidate that has since left the ladder is ignored and no
   candidate is ever skipped.
3. **Determinism.** The ranking is a pure function of the checked-in artifact,
   so a checkout fully determines the search order. A run never rewrites the
   artifact unless it is asked to with `bridge.py
   --record-tactic-search-history`; `--no-tactic-search-history` probes the
   declared order.
4. **What is recorded.** Only adoptions whose regenerated theorem then passed
   the real `lake build` are recorded, so the ranking can never be biased
   towards a tactic that merely type-checked in the probe module. Recording
   re-reads the artifact and merges the run's successes into it, so it is
   additive even when the run itself probed the declared order with
   `--no-tactic-search-history`.
5. **Malformed state.** A missing, unreadable, non-matching-schema or
   structurally invalid artifact learns nothing and the declared ladder order is
   used; the search never fails because of its history.
6. **Soundness.** Because a permutation cannot make an unprovable goal provable,
   the learned order changes only *which* tactic is found first (and how fast),
   never whether promotion is allowed — that still requires the real `lake
   build` of §12.4.

## 13. External proof injection (AI / handwritten proof bodies)

`scripts/external_proof.py` lets a caller — today mumei-agent's
`agent/lean_ai_proof.py` (`lean_fallback_strategy = "ai_generated_proof"`) —
supply a proof body for one atom. It generalises `IngestedAtom.auto_tactic`
(§12): both are exposed through `IngestedAtom.proof_body_override` and replace
only the generic `mumei_arith` / `mumei_arith_deep` tactic that
`render_theorem` would emit after `:= by`.

Input is a JSON file passed as `--external-proofs PATH` to `scripts/bridge.py`
or `scripts/ingest_cert.py`:

```json
{"proofs": [{"atom": "quintic_pos", "module_key": "std/quintic",
             "tactic_script": "intro hx\nsubst h_body\n...",
             "source": "ai_generated_proof", "attempts": 3}]}
```

Exactly one of `tactic_script` or `witness_lemma` (rendered as
`exact <lemma>`) is required; `module_key` is optional and scopes the proof to
one module; `source` is `ai_generated_proof` (default) or
`handwritten_witness`.

### 13.1 What the supplier does *not* control

1. **The statement.** The theorem header, binders, `def <atom>Result` and the
   translator IR are regenerated from the certificate exactly as without a
   proof; the supplier only fills the tactic block. An unfaithful statement
   (`partial_translation`) stays partial even with a proof attached and is
   never promoted.
2. **The gate.** Promotion still requires the real `lake build` and every
   `scripts/export_cert.py` contract gate (§9/§12.4). No code path marks an
   atom `lean_verified` because a proof was supplied.
3. **Tactic search.** Atoms with an external proof are not probed by §12
   (`is_search_eligible` is false), so a rejected or failing external proof
   cannot be silently replaced by a ladder tactic in the same run.

### 13.2 Rejection before rendering

`reject_external_proof` refuses a proof *before* it reaches a `.lean` file when
it is empty, uses both/neither body forms, names an invalid witness lemma, has
an unknown `source`, or contains any token from `FORBIDDEN_TACTIC_TOKENS`
(mirrors mumei-agent's list: `sorry`, `admit`, `axiom`, `unsafe`,
`implemented_by`, `@[extern`, `native_decide`, `run_cmd`, `run_tac`,
`#eval`/`#exit`/`#print`, `set_option`, `initialize`, macro/elab/syntax
keywords, `IO.`, and any new declaration line). A rejected atom keeps the status
it would have had without the proof (generic tactic, or
`manual_lemma_required` when it has a `manual_lemma_reason`), and its
`lean_metadata.external_proof` is `{"rejected": "<reason>"}`.

### 13.3 Metadata and provenance

For every atom that had an external proof supplied (accepted or rejected) the
per-atom `lean_metadata` gains:

| key | value |
| --- | --- |
| `external_proof` | `{source, script_sha256, witness_lemma?, attempts?, supersedes_manual_lemma_reason?}` or `{rejected}` |
| `ai_proof_used` | `true` only when `source == "ai_generated_proof"` **and** the atom is `lean_verified` by the real build; `false` for rejected, failed, handwritten |
| `ai_proof_attempts` | copied from `attempts` when present |
| `diagnostics` | `external_proof_source=<source>` or `external_proof_rejected=<reason>` |

`ai_proof_used` / `ai_proof_attempts` are the keys mumei-agent already writes
into its own `lean_metadata`; no new alias is introduced. Atoms without an
external proof keep their existing metadata shape. `translator_version` and
`bridge_lemma_hash` are unaffected — the bridge lemma catalog is not touched.

### 13.4 No-false-promotion matrix

`tests/test_lean_bridge_e2e.py::test_external_proof_matrix_never_promotes_unproved_atoms`
runs the live bridge over `tests/fixtures/std_quintic_external_proof.proof-cert.json`
(`x > 0 → x⁵ > 0`, which the generic ladder cannot close):

| supplied proof | `z3_check_result` | `ai_proof_used` |
| --- | --- | --- |
| valid tactic script | `lean_verified` | `true` |
| script containing `sorry` | `unknown` / `manual_lemma_required` (rejected, never rendered) | `false` |
| script leaving unsolved goals | `unknown` / `manual_lemma_required` | `false` |
| script with a type mismatch | `unknown` / `manual_lemma_required` | `false` |
| witness lemma that does not exist | `unknown` / `manual_lemma_required` | `false` |

## README translator contract

External **Lean 4** proof backend for the [mumei](https://github.com/mumei-lang/mumei)
formal verification language.

mumei verifies `requires`/`ensures` contracts automatically with the Z3 SMT
solver. For most atoms this is enough, but Z3 can return `unknown` on
contracts that lie beyond its decidable fragments — quantifier-heavy
properties, deep recursion, or domains like cryptographic primitives where a
hand-written proof is unavoidable.

`mumei-lean` is the *external complement*: it picks up those `unknown` atoms,
re-states them in Lean 4, lets you (or `mathlib4`) discharge the proof
obligation, and emits a mumei-compatible `.lean-cert.json` certificate that
the mumei resolver consumes through its existing
[Proof Certificate Chain (P5-A)](https://github.com/mumei-lang/mumei/blob/main/docs/PROOF_CERTIFICATE.md)
and `MUMEI_PROOF_BUNDLE` machinery (SI-5 Phase 3-C). The bridge now preserves
the typed Lean translator contract: `TranslatorIRMetadata`, binder mappings,
bridge lemma hashes, and manual lemma reasons move through ingestion, Lean
checking, and certificate export as auditable metadata.

For P9-G NLAE integration, `mumei-lean` is the **Fidelity Checker**: it
confirms that the reconstructed `.mm` obligation promoted by mumei-agent and
mumei can be exported as a `lean_verified` certificate, including live generated
theorem paths when they build successfully.

Cross-project vocabulary follows `mumei-lang/mumei/docs/CROSS_PROJECT_ROADMAP.md`: `harness_contract`, `intent_fidelity`, `artifact_paths`, `budget_policy_fingerprint`, and `lean_verified` are the canonical field names. Lean fallback documentation in this repo and `mumei-agent/docs/ROADMAP.md` must describe the same contract. The docs-sync contract is pinned by `tests/test_contract_vocabulary.py` so `lean_verified`, `stale_translator`, `translator_version`, and `bridge_lemma_hash` do not drift.

Translator contract updates are spec-first: every new
`TranslatorIRBinder.mumei_type`, `TranslatorIR.lowering_rules` entry, or bridge
lemma name must be documented in `docs/LEAN_TRANSLATOR_SPEC.md` before the
Python bridge emits it. `lean_verified` means a theorem built cleanly with the
current `translator_version` and `bridge_lemma_hash`; `stale_translator` means
that version/hash no longer matches. Array lowering now records both
`mumei_array_bounds_bridge` and `mumei_array_get_bridge`, while integer
machine-range obligations continue to use `mumei_i64_overflow_bridge`.

> mumei's "fully automatic verification" philosophy is preserved. mumei-lean
> only steps in for the slice of contracts Z3 cannot close on its own, and the
> mumei compiler itself requires **zero changes** to consume the resulting
> certificates: they piggy-back on the existing 3-tier resolver lookup.
