import SqueezeBench.Problems.Roth.Records.Lower.V000.Def

/-!
# Roth lower-bound record V000 — validity

No witness set is constructed. `f` is computable at these sizes, so `f 1 = 1` and `f 2 = 2` are
settled by the kernel, and `f_mono` carries the second to every `n ≥ 2`.
-/

namespace SqueezeBench.Roth.Lower.V000

open SqueezeBench

theorem valid : LowerBoundHolds f record :=
  pin_lowerBoundHolds fun n hn => by
    have hn1 : (1 : ℕ) ≤ n := hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have hone : n = 1 := by omega
      subst hone
      have h1 : f 1 = 1 := by decide
      omega
    · have h2 : f 2 = 2 := by decide
      have hm := f_mono (show nMin ≤ 2 by simp) h
      omega

end SqueezeBench.Roth.Lower.V000
