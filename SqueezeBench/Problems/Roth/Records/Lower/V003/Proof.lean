import SqueezeBench.Problems.Roth.Records.Lower.V003.Def
import SqueezeBench.Problems.Roth.Records.Lower.V002.Proof

/-! Record V003 for Roth, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V003.lean`. -/

namespace SqueezeBench.Roth.Lower.V003

open SqueezeBench Finset

-- `{0, 1, 3, 7, 8}` is 3-AP-free: no two of its elements average to a third
theorem five_le_f_nine : 5 ≤ SqueezeBench.Roth.f 9 := by
  refine SqueezeBench.Roth.le_f_of_threeAPFree (by simp) {0, 1, 3, 7, 8} ?_ ?_ (by decide)
  · intro a ha b hb c hc h
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
    omega
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    omega

-- the record's recursion is a valid lower bound as soon as the fuel suffices
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
    · exact SqueezeBench.Roth.Lower.V002.cnt_valid n
    · split
      · rename_i h9
        subst h9
        exact five_le_f_nine
      · rename_i h8 h9
        have h10 : 10 ≤ n := by omega
        have h₁ := ih ((n + 2) / 3) (by omega)
        have h₂ := ih ((n + 1) / 3) (by omega)
        have := SqueezeBench.Roth.Lower.V002.split_le n (by omega)
        omega

theorem cnt_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f cnt :=
  fun n => cntAux_le n n le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  maxWith_valid SqueezeBench.Roth.Lower.V002.valid cnt_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V002.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V002.record record :=
  maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Roth.Lower.V003
