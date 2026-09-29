import SqueezeBench.Problems.Roth.Records.Upper.V000.Def

/-!
# Roth upper-bound record V000 — validity
-/

namespace SqueezeBench.Roth.Upper.V000

open SqueezeBench

theorem valid : UpperBoundHolds f record := fun n => f_le_self n

end SqueezeBench.Roth.Upper.V000
