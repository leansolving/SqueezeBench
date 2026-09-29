import SqueezeBench.Problems.HypercubeC4.Records.Upper.V003.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V002.Proof

/-! Record V003 for HypercubeC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V003.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V003

open Finset SimpleGraph

-- `Q₂` is a single square, so a `C₄`-free subgraph must miss one of its four edges.
theorem f_two_le : SqueezeBench.HypercubeC4.f 2 ≤ 3 := by
  refine f_le_of_forall_not_hasSquare (by rw [nMin_eq]; norm_num) fun G _ hle hG => ?_
  by_contra hlt
  have hsub : G.edgeFinset ⊆ (hypercube 2).edgeFinset := SimpleGraph.edgeFinset_mono hle
  have hQ : #(hypercube 2).edgeFinset = 4 := by decide
  have heq : G = hypercube 2 :=
    SimpleGraph.edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le hsub (by omega))
  subst heq
  exact hG ⟨![false, false], 0, 1, by decide, hypercube_adj.2 (by decide),
    hypercube_adj.2 (by decide), hypercube_adj.2 (by decide), hypercube_adj.2 (by decide)⟩

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.patch_valid' SqueezeBench.HypercubeC4.Upper.V002.valid f_two_le

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V002.record record :=
  SqueezeBench.patch_improves' (by decide)

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V002.record record :=
  SqueezeBench.patch_strict' (by decide) (by decide)

end SqueezeBench.HypercubeC4.Upper.V003
