import Mathlib.Tactic
import MumeiLean.Basic

/-!
# MumeiLean.Quantifiers

Quantifier manipulation lemmas for contract expressions emitted by the bridge
translator. Covers skolemization patterns, herbrandization helpers, and
bounded↔unbounded conversion lemmas that the `mumei_arith` tactic cascade
cannot close automatically.
-/

namespace MumeiLean.Quantifiers

/-! ### Skolemization / Herbrandization -/

theorem skolemize_exists (P : Int → Prop)
    (hex : ∃ x : Int, P x) :
    ∃ x : Int, P x := hex

theorem herbrand_forall (P : Int → Prop)
    (hall : ∀ x : Int, P x) (t : Int) :
    P t := hall t

theorem skolemize_bounded_exists (lo hi : Int) (P : Int → Prop)
    (hex : ∃ x : Int, lo ≤ x ∧ x < hi ∧ P x) :
    ∃ x : Int, lo ≤ x ∧ x < hi ∧ P x := hex

theorem herbrand_bounded_forall (lo hi : Int) (P : Int → Prop)
    (hall : ∀ x : Int, lo ≤ x → x < hi → P x) (t : Int)
    (hlo : lo ≤ t) (hhi : t < hi) :
    P t := hall t hlo hhi

/-! ### Bounded ↔ Unbounded conversions -/

theorem bounded_forall_of_unrestricted (lo hi : Int) (P : Int → Prop)
    (huniv : ∀ x : Int, P x) :
    ∀ x : Int, lo ≤ x → x < hi → P x := by
  intros; exact huniv _

theorem bounded_exists_of_witness (lo hi : Int) (P : Int → Prop)
    (w : Int) (hlo : lo ≤ w) (hhi : w < hi) (hp : P w) :
    ∃ x : Int, lo ≤ x ∧ x < hi ∧ P x :=
  ⟨w, hlo, hhi, hp⟩

/-! ### Quantifier composition helpers -/

theorem forall_and_split (P Q : Int → Prop)
    (hp : ∀ x : Int, P x) (hq : ∀ x : Int, Q x) :
    ∀ x : Int, P x ∧ Q x := by
  intro x; exact ⟨hp x, hq x⟩

theorem exists_or_left (P Q : Int → Prop)
    (hp : ∃ x : Int, P x) :
    ∃ x : Int, P x ∨ Q x := by
  rcases hp with ⟨x, hx⟩; exact ⟨x, Or.inl hx⟩

theorem forall_implies_trans (P Q R : Int → Prop)
    (hpq : ∀ x : Int, P x → Q x) (hqr : ∀ x : Int, Q x → R x) :
    ∀ x : Int, P x → R x := by
  intro x hp; exact hqr x (hpq x hp)

/-! ### List-based quantification -/

theorem forall_list_nil (P : Int → Prop) :
    ∀ x : Int, x ∈ ([] : List Int) → P x := by
  intro _ h; exact absurd h (List.not_mem_nil _)

theorem forall_list_cons (P : Int → Prop) (a : Int) (as : List Int)
    (ha : P a) (has : ∀ x : Int, x ∈ as → P x) :
    ∀ x : Int, x ∈ (a :: as) → P x := by
  intro x hx
  cases List.mem_cons.mp hx with
  | inl h => rw [h]; exact ha
  | inr h => exact has x h

theorem exists_list_witness (P : Int → Prop) (xs : List Int)
    (w : Int) (hmem : w ∈ xs) (hp : P w) :
    ∃ x : Int, x ∈ xs ∧ P x :=
  ⟨w, hmem, hp⟩

/-! ### Nested quantifier rewriting -/

theorem forall_forall_comm (P : Int → Int → Prop)
    (h : ∀ x y : Int, P x y) :
    ∀ y x : Int, P x y := by
  intro y x; exact h x y

theorem exists_exists_comm (P : Int → Int → Prop)
    (hex : ∃ x : Int, ∃ y : Int, P x y) :
    ∃ y : Int, ∃ x : Int, P x y := by
  rcases hex with ⟨x, y, hxy⟩; exact ⟨y, x, hxy⟩

theorem forall_exists_swap_of_finite (P : Int → Int → Prop)
    (_h : ∀ x : Int, ∃ y : Int, P x y)
    (hchoice : ∃ f : Int → Int, ∀ x : Int, P x (f x)) :
    ∃ f : Int → Int, ∀ x : Int, P x (f x) := hchoice

/-! ### Implication as Prop -/

theorem mumei_implies_intro (P Q : Prop) (h : P → Q) : P → Q := h

theorem mumei_implies_elim (P Q : Prop) (hpq : P → Q) (hp : P) : Q := hpq hp

theorem mumei_iff_intro (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : P ↔ Q :=
  ⟨hpq, hqp⟩

end MumeiLean.Quantifiers
