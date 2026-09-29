import Mathlib
import SqueezeBench.Core

/-!
# Roth numbers `r₃(n)`

`f n` is the largest size of a subset of `{0, …, n-1}` containing no three-term arithmetic
progression. See OEIS A003002.

`f` reuses Mathlib's `rothNumberNat`, which *is* this quantity:
`rothNumberNat n = addRothNumber (Finset.range n)`, a `Nat.findGreatest` over the subsets of
`range n` satisfying `ThreeAPFree`. Nothing is redefined here.

Two consequences. The supremum is over a `Fintype` and the empty set always qualifies, so `f`
is total and needs no nonemptiness lemma. And `f` is **computable**, so the known values below
are checked by the build rather than cited.
-/

namespace SqueezeBench.Roth

open Finset

/-- Smallest meaningful parameter value. At `n = 0` the range is empty and `f 0 = 0`. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- The largest 3-AP-free subset of `{0, …, n-1}`, pinned to `0` below `nMin`. -/
def f (n : ℕ) : ℕ := if n < nMin then 0 else rothNumberNat n

theorem f_of_le {n : ℕ} (hn : nMin ≤ n) : f n = rothNumberNat n := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]

/-- Lower bounds reduce to exhibiting a 3-AP-free subset of `{0, …, n-1}`. -/
theorem le_f_of_threeAPFree {n k : ℕ} (hn : nMin ≤ n) (s : Finset ℕ)
    (hs : ThreeAPFree (s : Set ℕ)) (hlt : ∀ x ∈ s, x < n) (hcard : s.card = k) : k ≤ f n := by
  rw [f_of_le hn]
  exact ThreeAPFree.le_rothNumberNat s hs hlt hcard

/-- The ambient bound `r₃(n) ≤ n`, free from `rothNumberNat_le`. -/
theorem f_le_self (n : ℕ) : f n ≤ n := by
  rw [f]
  split
  · exact Nat.zero_le _
  · exact rothNumberNat_le n

/-- Monotonicity, inherited from `rothNumberNat`. A lower bound proved at one `n` therefore
transfers to every larger one, which is what the seed record uses. -/
theorem f_mono {m n : ℕ} (hm : nMin ≤ m) (h : m ≤ n) : f m ≤ f n := by
  rw [f_of_le hm, f_of_le (le_trans hm h)]
  exact rothNumberNat.monotone h

/-! ## Known values

`f` is computable, so these are checked on every build rather than tabulated. They agree with
A003002. The kernel cost grows as `2 ^ n`, so `n = 4` is the practical limit here; further
values are cited in the README. -/

set_option maxRecDepth 10000 in
example : f 1 = 1 := by decide

set_option maxRecDepth 100000 in
example : f 2 = 2 := by decide

set_option maxRecDepth 400000 in
example : f 3 = 2 := by decide

set_option maxRecDepth 1000000 in
example : f 4 = 3 := by decide

end SqueezeBench.Roth
