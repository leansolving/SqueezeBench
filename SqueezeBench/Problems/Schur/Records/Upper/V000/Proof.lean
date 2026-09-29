import SqueezeBench.Problems.Schur.Records.Upper.V000.Def
import SqueezeBench.Problems.Schur.Finite

/-!
# Schur upper-bound record V000 — validity
-/

namespace SqueezeBench.Schur.Upper.V000

open SqueezeBench Finset

theorem valid : UpperBoundHolds f record := by
  intro k
  rcases Nat.lt_or_ge k nMin with h | h
  · rw [f, if_pos h]
    exact Nat.zero_le _
  · have hle := f_le_of_forces h (forces_factorial h)
    have hfp : 0 < Nat.factorial k := Nat.factorial_pos k
    have heq : 3 * Nat.factorial k - 1 - 1 = 3 * Nat.factorial k - 2 := by omega
    rwa [heq] at hle

end SqueezeBench.Schur.Upper.V000
