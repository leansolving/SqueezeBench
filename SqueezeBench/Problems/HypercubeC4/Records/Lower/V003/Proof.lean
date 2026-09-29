import SqueezeBench.Problems.HypercubeC4.Records.Lower.V003.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V002.Proof

/-! Record V003 for HypercubeC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V003.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V003

open Finset SimpleGraph

-- A word read as a binary numeral, so that an edge can be named by a pair of numbers.
def code {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0

-- The cube with the edges listed in `L` deleted.
def cut (n : ℕ) (L : List (ℕ × ℕ)) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1 ∧ ¬ ((code x, code y) ∈ L ∨ (code y, code x) ∈ L)
  symm := ⟨fun x y h => ⟨by rw [hammingDist_comm]; exact h.1, fun hb => h.2 hb.symm⟩⟩
  loopless := ⟨fun x h => absurd h.1 (by simp)⟩

instance decCut (n : ℕ) (L : List (ℕ × ℕ)) : DecidableRel (cut n L).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1 ∧
    ¬ ((code x, code y) ∈ L ∨ (code y, code x) ∈ L)))

theorem cut_le (n : ℕ) (L : List (ℕ × ℕ)) : cut n L ≤ HypercubeC4.hypercube n := fun _ _ h => h.1

-- Three edges of `Q₃` meeting all six of its squares.
def L3 : List (ℕ × ℕ) := [(0, 1), (2, 6), (5, 7)]

-- Eight edges of `Q₄` meeting all twenty-four of its squares.
def L4 : List (ℕ × ℕ) :=
  [(0, 1), (2, 6), (3, 11), (4, 12), (5, 7), (8, 10), (9, 13), (14, 15)]

theorem nine_le : 9 ≤ SqueezeBench.HypercubeC4.f 3 := by
  have h := HypercubeC4.le_f_of_not_hasSquare (G := cut 3 L3)
    (by rw [HypercubeC4.nMin_eq]; omega) (cut_le 3 L3)
    (by unfold HypercubeC4.HasSquare; decide)
  have hc : ((cut 3 L3).edgeFinset).card = 9 := by decide
  omega

theorem twentyfour_le : 24 ≤ SqueezeBench.HypercubeC4.f 4 := by
  have h := HypercubeC4.le_f_of_not_hasSquare (G := cut 4 L4)
    (by rw [HypercubeC4.nMin_eq]; omega) (cut_le 4 L4)
    (by unfold HypercubeC4.HasSquare; decide)
  have hc : ((cut 4 L4).edgeFinset).card = 24 := by decide
  omega

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.patch_valid (SqueezeBench.patch_valid V002.valid nine_le) twentyfour_le

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V002.record record :=
  SqueezeBench.ImprovesLower.trans (SqueezeBench.patch_improves (by decide))
    (SqueezeBench.patch_improves (by decide))

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V002.record record :=
  ⟨4, by decide, by decide⟩

end SqueezeBench.HypercubeC4.Lower.V003
