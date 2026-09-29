import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V000.Def

/-!
# Ruzsa–Szemerédi upper-bound record V000 — validity
-/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V000

open SqueezeBench

theorem valid : UpperBoundHolds f record := fun n => f_le_choose_three n

end SqueezeBench.RuzsaSzemeredi.Upper.V000
