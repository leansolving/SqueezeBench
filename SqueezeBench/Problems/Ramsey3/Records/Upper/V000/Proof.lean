import SqueezeBench.Problems.Ramsey3.Records.Upper.V000.Def

/-!
# `R(3,k)` upper-bound record V000 — validity
-/

namespace SqueezeBench.Ramsey3.Upper.V000

open SqueezeBench

theorem valid : UpperBoundHolds f record := by
  intro k
  rcases Nat.lt_or_ge k nMin with h | h
  · rw [f, if_pos h]
    exact Nat.zero_le _
  · have hk : (2 : ℕ) ≤ k := h
    exact f_le_of_forces h (forces_choose_three (by omega))

end SqueezeBench.Ramsey3.Upper.V000
