import Mathlib.Data.List.Sort

/-!
# MumeiLean.Sort

Bridge lemmas for sort-ascending preservation obligations escalated from
the mumei verifier when Z3 cannot discharge `forall(i, 0, n-1, arr[i] <= arr[i+1])`
on an insertion sort body (Array + forall quantifier timeout / spurious
counterexample).

Formal spec: `docs/LEAN_TRANSLATOR_SPEC.md` section 5.11.

The mumei atom `verified_insertion_sort_ascending` has:
- requires: `n >= 0 && forall(i, 0, n, arr[i] >= 0)`
- ensures:  `result == n && forall(i, 0, result - 1, arr[i] <= arr[i + 1])`
- body:     insertion sort algorithm

Z3 produces a spurious counterexample on the `forall` ensures, so the
obligation is escalated to Lean. The bridge connects the mumei contract
surface to mathlib's `List.insertionSort` and `List.Sorted`.
-/

namespace MumeiLean.Sort

/-- `List.insertionSort (· ≤ ·)` on `Int` produces a `List.Sorted` output
    with the same length as the input.

    This is the core bridge lemma used by the generated theorem for
    `verified_insertion_sort_ascending`. -/
theorem insertion_sort_ascending_bridge (arr : List Int) :
    (List.insertionSort (· ≤ ·) arr).length = arr.length ∧
    List.Sorted (· ≤ ·) (List.insertionSort (· ≤ ·) arr) :=
  ⟨List.length_insertionSort _ _, List.sorted_insertionSort _ _⟩

/-- Pointwise consequence of `List.Sorted`: adjacent elements satisfy
    the ordering relation. Used to lower `forall(i, 0, n-1, arr[i] <= arr[i+1])`
    from the mumei ensures surface to the `List.Sorted` bridge. -/
theorem sorted_adjacent_le {arr : List Int}
    (hs : List.Sorted (· ≤ ·) arr)
    {i j : Fin arr.length}
    (hij : i < j) :
    arr.get i ≤ arr.get j :=
  List.Sorted.rel_get_of_lt hs hij

end MumeiLean.Sort
