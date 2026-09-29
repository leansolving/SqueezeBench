import SqueezeBench.Problems.ExGirthFive.Records.Lower.V000.Def

/-!
# ExGirthFive lower-bound record V000 — validity
-/

namespace SqueezeBench.ExGirthFive.Lower.V000

open SqueezeBench

theorem valid : LowerBoundHolds f record := fun _ => Nat.zero_le _

end SqueezeBench.ExGirthFive.Lower.V000
