import SqueezeBench.Problems.HypercubeC4.Records.Lower.V004.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V003.Proof

/-! Record V004 for HypercubeC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V004.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V004

open Finset SimpleGraph

-- Twenty-five edges of `Q₅` meeting all eighty of its squares.
def L5 : List (ℕ × ℕ) :=
  [(0, 1), (0, 4), (1, 9), (2, 18), (3, 7), (4, 5), (6, 14), (7, 23), (8, 10), (9, 25),
   (10, 11), (11, 27), (12, 13), (12, 28), (13, 15), (16, 24), (17, 19), (17, 21), (18, 19),
   (20, 22), (21, 29), (24, 25), (26, 30), (27, 31), (30, 31)]

theorem fiftyfive_le : 55 ≤ SqueezeBench.HypercubeC4.f 5 := by
  have h := HypercubeC4.le_f_of_not_hasSquare (G := V003.cut 5 L5)
    (by rw [HypercubeC4.nMin_eq]; omega) (V003.cut_le 5 L5)
    (by unfold HypercubeC4.HasSquare; decide)
  have hc : ((V003.cut 5 L5).edgeFinset).card = 55 := by decide
  omega

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.patch_valid V003.valid fiftyfive_le

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V003.record record :=
  SqueezeBench.patch_improves (by decide)

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V003.record record :=
  ⟨5, by decide, by decide⟩

end SqueezeBench.HypercubeC4.Lower.V004
