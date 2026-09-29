import SqueezeBench.Problems.ExGirthFive.Records.Upper.V000.Def

/-!
# ExGirthFive upper-bound record V000 — validity
-/

namespace SqueezeBench.ExGirthFive.Upper.V000

open SqueezeBench

theorem valid : UpperBoundHolds f record := fun n => f_le_choose_two n

end SqueezeBench.ExGirthFive.Upper.V000
