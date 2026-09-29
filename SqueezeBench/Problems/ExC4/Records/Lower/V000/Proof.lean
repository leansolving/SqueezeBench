import SqueezeBench.Problems.ExC4.Records.Lower.V000.Def

/-!
# ExC4 lower-bound record V000 — validity
-/

namespace SqueezeBench.ExC4.Lower.V000

open SqueezeBench

theorem valid : LowerBoundHolds f record := fun _ => Nat.zero_le _

end SqueezeBench.ExC4.Lower.V000
