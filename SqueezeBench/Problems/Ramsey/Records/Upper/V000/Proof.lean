import SqueezeBench.Problems.Ramsey.Records.Upper.V000.Def
import SqueezeBench.Problems.Ramsey.Finite

/-!
# Ramsey upper-bound record V000 — validity
-/

namespace SqueezeBench.Ramsey.Upper.V000

open SqueezeBench SimpleGraph

theorem valid : UpperBoundHolds f record := by
  intro n
  rcases Nat.lt_or_ge n nMin with h | h
  · rw [f, if_pos h]
    exact Nat.zero_le _
  · exact f_le_of_forces h (forces_choose n)

end SqueezeBench.Ramsey.Upper.V000
