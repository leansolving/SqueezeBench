import SqueezeBench.Problems.ExC4.Records.Upper.V000.Def

/-!
# ExC4 upper-bound record V000 — validity
-/

namespace SqueezeBench.ExC4.Upper.V000

open SqueezeBench

theorem valid : UpperBoundHolds f record := fun n => f_le_choose_two n

end SqueezeBench.ExC4.Upper.V000
