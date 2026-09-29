import SqueezeBench.Problems.Tutorial.Records.Lower.V000.Def

/-!
# Tutorial lower-bound record V000 — validity

`{1} ⊆ {1, …, m}` is doubling-free, so it witnesses `g m ≥ 1` for every `m ≥ nMin`.
-/

namespace SqueezeBench.Tutorial.Lower.V000

open SqueezeBench Finset

theorem valid : LowerBoundHolds f record := by
  intro m
  rcases Nat.lt_or_ge m nMin with h | h
  · have hm0 : m = 0 := by simpa using h
    subst hm0
    simp [record, f]
  · have hm : 1 ≤ m := by simpa using h
    show (if m < nMin then 0 else 1) ≤ f m
    rw [if_neg (Nat.not_lt.mpr h)]
    refine le_f_of_le_g h ?_
    have hsub : ({1} : Finset ℕ) ⊆ Icc 1 m := by
      intro x hx
      simp only [mem_singleton] at hx
      subst hx
      simp only [mem_Icc]
      omega
    have havoid : AvoidsDoubling ({1} : Finset ℕ) := by
      intro x hx
      simp only [mem_singleton] at hx ⊢
      omega
    simpa using card_le_g hsub havoid

end SqueezeBench.Tutorial.Lower.V000
