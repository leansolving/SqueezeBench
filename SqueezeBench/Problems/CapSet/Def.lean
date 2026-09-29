import Mathlib
import SqueezeBench.Core

/-!
# Cap sets in `F₃ⁿ`

A *cap* is a subset of `F₃ⁿ` containing no three distinct collinear points, equivalently
no nontrivial three-term arithmetic progression. `f n` is the largest size of a cap.
See OEIS A090245.

Mathlib's `ThreeAPFree` **is** this condition on `Fin n → ZMod 3`: it unfolds to
`∀ a b c ∈ A, a + c = b + b → a = b`, and over `ZMod 3` a triple with `a + c = 2b` and
`a = b` forces `c = b` too, so exactly the nontrivial progressions are excluded.

This `f` is total by construction: `addRothNumber` is `Nat.findGreatest` over a finite
type, and the empty subset always qualifies, so no nonemptiness lemma is needed.
-/

namespace SqueezeBench.CapSet

open Finset

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- The largest size of a cap in `F₃ⁿ`, pinned to `0` below `nMin`.

This `f` is computable, the search being finite, and evaluates to `2` at `n = 1` and `4`
at `n = 2`, matching A090245. The known values continue `9, 20, 45, 112` for
`n = 3, …, 6`, but those are far beyond what this definition can be evaluated at — the
search space is `2^(3^n)`. -/
def f (n : ℕ) : ℕ :=
  if n < nMin then 0 else addRothNumber (univ : Finset (Fin n → ZMod 3))

/-- Lower bounds reduce to exhibiting a cap. Wraps `ThreeAPFree.le_addRothNumber`. -/
theorem le_f_of_threeAPFree {n : ℕ} {A : Finset (Fin n → ZMod 3)} (hn : nMin ≤ n)
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) : A.card ≤ f n := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  exact hA.le_addRothNumber (subset_univ A)

/-- Upper bounds reduce to ruling out caps of a given size.
Wraps `addRothNumber_lt_of_forall_not_threeAPFree`. -/
theorem f_lt_of_forall_not {n k : ℕ} (hn : nMin ≤ n)
    (h : ∀ A ∈ powersetCard k (univ : Finset (Fin n → ZMod 3)),
      ¬ ThreeAPFree (A : Set (Fin n → ZMod 3))) : f n < k := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  exact addRothNumber_lt_of_forall_not_threeAPFree h

/-! ## Known values

`f` is computable, so the two values within reach are checked here rather than asserted.
They agree with OEIS A090245, which is evidence that this definition denotes the intended
object. The search space is `2^(3^n)`, so `n = 2` is the practical limit. -/

example : f 1 = 2 := by decide

set_option maxRecDepth 100000 in
example : f 2 = 4 := by decide

/-- The ambient bound `|F₃ⁿ| = 3ⁿ`, free from `Nat.findGreatest_le`. -/
theorem f_le_card (n : ℕ) : f n ≤ 3 ^ n := by
  rw [f]
  split
  · exact Nat.zero_le _
  · calc addRothNumber (univ : Finset (Fin n → ZMod 3))
        ≤ (univ : Finset (Fin n → ZMod 3)).card := addRothNumber_le _
      _ = 3 ^ n := by simp

end SqueezeBench.CapSet
