import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V006.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V005.Proof

/-! Record V006 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the three obligations.
Two more explicit 3-AP-free sets extend V005's table; the recursion and its proof are V005's,
with `V005.base_le` covering the entries below `M = 51`. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V006

open SqueezeBench

theorem r51 : 17 ≤ rothNumberNat 51 :=
  V005.le_roth_of (s := {0, 1, 3, 4, 10, 12, 13, 15, 28, 32, 34, 35, 37, 45, 47, 48, 50})
    (by decide) (by decide) (by decide)

theorem r69 : 20 ≤ rothNumberNat 69 :=
  V005.le_roth_of
    (s := {0, 1, 4, 6, 10, 15, 17, 18, 22, 23, 25, 47, 48, 52, 54, 55, 59, 65, 67, 68})
    (by decide) (by decide) (by decide)

theorem base_le (m : ℕ) : base m ≤ rothNumberNat m := by
  unfold base
  split_ifs with h1 h2
  · exact V005.base_le m
  · exact le_trans r51 (rothNumberNat.monotone (by omega))
  · exact le_trans r69 (rothNumberNat.monotone (by omega))

theorem szAux_le : ∀ fuel m, m ≤ fuel → szAux fuel m ≤ rothNumberNat m
  | 0, m, _ => by simp [szAux]
  | fuel + 1, m, h => by
      rw [szAux]
      split
      · have h1 := V001.min_two_le_rothNumberNat m
        omega
      · rename_i hm2
        have hb := base_le m
        have hf1 : (m + 2) / 3 ≤ fuel := by omega
        have hf2 : (m + 1) / 3 ≤ fuel := by omega
        have ih1 := szAux_le fuel ((m + 2) / 3) hf1
        have ih2 := szAux_le fuel ((m + 1) / 3) hf2
        have hsplit := V004.roth_split m
        omega

theorem sz_le (m : ℕ) : sz m ≤ rothNumberNat m := szAux_le m m le_rfl

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f v := by
  intro n
  by_cases hn : 3 ≤ n
  · have hle : 6 * V001.blocks n + 3 ≤ n := by unfold V001.blocks; omega
    calc v n = (2 * V001.blocks n + 1) * sz (V001.blocks n) := rfl
      _ ≤ (2 * V001.blocks n + 1) * rothNumberNat (V001.blocks n) :=
          Nat.mul_le_mul_left _ (sz_le _)
      _ ≤ SqueezeBench.RuzsaSzemeredi.f (6 * V001.blocks n + 3) := V001.key _
      _ ≤ SqueezeBench.RuzsaSzemeredi.f n :=
          SqueezeBench.RuzsaSzemeredi.f_mono
            (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]; omega) hle
  · have h0 : V001.blocks n = 0 := by unfold V001.blocks; omega
    simp [v, h0, sz, szAux]

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record :=
  maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V005.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V005.record record :=
  maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 417) (by decide) (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V006
