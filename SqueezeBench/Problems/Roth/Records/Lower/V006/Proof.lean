import SqueezeBench.Problems.Roth.Records.Lower.V006.Def
import SqueezeBench.Problems.Roth.Records.Lower.V005.Proof

/-! Record V006 for Roth, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V006.lean`. -/

namespace SqueezeBench.Roth.Lower.V006

open SqueezeBench Finset

theorem setC_le (n : ℕ) : SqueezeBench.Roth.Lower.V004.below setC n ≤ SqueezeBench.Roth.f n :=
  SqueezeBench.Roth.Lower.V004.below_le setC (by decide)
    (SqueezeBench.Roth.Lower.V004.free_of_all (by decide)) n

theorem setD_le (n : ℕ) : SqueezeBench.Roth.Lower.V004.below setD n ≤ SqueezeBench.Roth.f n :=
  SqueezeBench.Roth.Lower.V004.below_le setD (by decide)
    (SqueezeBench.Roth.Lower.V004.free_of_all (by decide)) n

theorem tbl_le (n : ℕ) : tbl n ≤ SqueezeBench.Roth.f n :=
  max_le (max_le (setC_le n) (setD_le n)) (SqueezeBench.Roth.Lower.V005.cnt_valid n)

-- monotonicity of `f`: the top of the base window survives to every larger `n`
theorem tbl56_le {n : ℕ} (hn : 56 ≤ n) : tbl 56 ≤ SqueezeBench.Roth.f n :=
  le_trans (tbl_le 56) (SqueezeBench.Roth.f_mono (show SqueezeBench.Roth.nMin ≤ 56 by simp) hn)

theorem cntAux_le : ∀ fuel n : ℕ, n ≤ fuel → cntAux fuel n ≤ SqueezeBench.Roth.f n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simp [cntAux, SqueezeBench.Roth.f]
  | succ fuel ih =>
    intro n hn
    rw [cntAux]
    split
    · exact tbl_le n
    · rename_i h56
      refine max_le (tbl56_le (by omega)) ?_
      have h₁ := ih ((n + 2) / 3) (by omega)
      have h₂ := ih ((n + 1) / 3) (by omega)
      have := SqueezeBench.Roth.Lower.V002.split_le n (by omega)
      omega

theorem cnt_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f cnt :=
  fun n => cntAux_le n n le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  maxWith_valid SqueezeBench.Roth.Lower.V005.valid cnt_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V005.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V005.record record :=
  maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 33) (by decide) (by decide)

end SqueezeBench.Roth.Lower.V006
