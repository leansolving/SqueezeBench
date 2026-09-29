import SqueezeBench.Problems.HypercubeC4.Records.Lower.V000.Def

/-!
# HypercubeC4 lower-bound record V000 — validity
-/

namespace SqueezeBench.HypercubeC4.Lower.V000

open SqueezeBench

theorem valid : LowerBoundHolds f record := fun _ => Nat.zero_le _

end SqueezeBench.HypercubeC4.Lower.V000
