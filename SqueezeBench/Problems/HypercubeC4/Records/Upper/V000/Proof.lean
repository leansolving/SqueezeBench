import SqueezeBench.Problems.HypercubeC4.Records.Upper.V000.Def

/-!
# HypercubeC4 upper-bound record V000 — validity
-/

namespace SqueezeBench.HypercubeC4.Upper.V000

open SqueezeBench

theorem valid : UpperBoundHolds f record := fun n => by
  refine (f_le_card_edgeFinset_hypercube n).trans ?_
  simpa [record] using SimpleGraph.card_edgeFinset_le_card_choose_two (G := hypercube n)

end SqueezeBench.HypercubeC4.Upper.V000
