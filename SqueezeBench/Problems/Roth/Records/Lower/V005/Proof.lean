import SqueezeBench.Problems.Roth.Records.Lower.V005.Def
import SqueezeBench.Problems.Roth.Records.Lower.V004.Proof

/-! Record V005 for Roth, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V005.lean`. -/

namespace SqueezeBench.Roth.Lower.V005

open SqueezeBench Finset

-- monotonicity of `f`: the base window's top value survives to every larger `n`
theorem tbl27_le {n : ℕ} (hn : 27 ≤ n) :
    SqueezeBench.Roth.Lower.V004.tbl 27 ≤ SqueezeBench.Roth.f n :=
  le_trans (SqueezeBench.Roth.Lower.V004.tbl_le 27)
    (SqueezeBench.Roth.f_mono (show SqueezeBench.Roth.nMin ≤ 27 by simp) hn)

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
    · exact SqueezeBench.Roth.Lower.V004.tbl_le n
    · rename_i h27
      refine max_le (tbl27_le (by omega)) ?_
      have h₁ := ih ((n + 2) / 3) (by omega)
      have h₂ := ih ((n + 1) / 3) (by omega)
      have := SqueezeBench.Roth.Lower.V002.split_le n (by omega)
      omega

theorem cnt_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f cnt :=
  fun n => cntAux_le n n le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  maxWith_valid SqueezeBench.Roth.Lower.V004.valid cnt_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V004.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V004.record record :=
  maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 28) (by decide) (by decide)

end SqueezeBench.Roth.Lower.V005
