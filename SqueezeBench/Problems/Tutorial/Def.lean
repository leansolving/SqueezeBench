import Mathlib
import SqueezeBench.Core

/-!
# Tutorial problem: doubling-free subsets

`g m` is the largest size of a subset of `{1, …, m}` containing no element together with
its double. Included to exercise the submission pipeline; not a leaderboard problem.

`g` is computable, so the mathematical obligation at a point can be discharged by
`decide`.
-/

namespace SqueezeBench.Tutorial

open Finset

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- `S` contains no element together with its double. -/
def AvoidsDoubling (S : Finset ℕ) : Prop := ∀ x ∈ S, 2 * x ∉ S

instance (S : Finset ℕ) : Decidable (AvoidsDoubling S) :=
  inferInstanceAs (Decidable (∀ x ∈ S, 2 * x ∉ S))

/-- The largest size of a doubling-free subset of `{1, …, m}`. -/
def g (m : ℕ) : ℕ :=
  ((Icc 1 m).powerset.filter AvoidsDoubling).sup Finset.card

/-- The target function, pinned to `0` below `nMin`. -/
def f (m : ℕ) : ℕ := if m < nMin then 0 else g m

/-! ## Known values

`f` is computable here, so its values are checked rather than cited. -/

set_option maxRecDepth 100000 in
example : (List.range 11).map (fun i => f (i + 1)) = [1, 1, 2, 3, 4, 4, 5, 5, 6, 6, 7] := by
  decide

/-- Any doubling-free subset witnesses a lower bound on `g m`. -/
theorem card_le_g {S : Finset ℕ} {m : ℕ}
    (hsub : S ⊆ Icc 1 m) (havoid : AvoidsDoubling S) : S.card ≤ g m :=
  Finset.le_sup (f := Finset.card) (by simp [mem_filter, mem_powerset, hsub, havoid])

/-- Above `nMin`, lower bounds on `f` reduce to lower bounds on `g`. -/
theorem le_f_of_le_g {m k : ℕ} (hm : nMin ≤ m) (h : k ≤ g m) : k ≤ f m := by
  simp only [f, if_neg (Nat.not_lt.mpr hm)]; exact h

end SqueezeBench.Tutorial
