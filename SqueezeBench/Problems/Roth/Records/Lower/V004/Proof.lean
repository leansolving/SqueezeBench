import SqueezeBench.Problems.Roth.Records.Lower.V004.Def
import SqueezeBench.Problems.Roth.Records.Lower.V003.Proof

/-! Record V004 for Roth, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V004.lean`. -/

namespace SqueezeBench.Roth.Lower.V004

open SqueezeBench Finset

-- a finite check of the `|l|³` triples certifies that `l` has no three-term progression
theorem free_of_all {l : List ℕ}
    (h : l.all (fun a => l.all (fun b => l.all (fun c =>
      decide (a + c ≠ b + b) || decide (a = c)))) = true) :
    ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, a + c = b + b → a = c := by
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  intro a ha b hb c hc hh
  have := h a ha b hb c hc
  omega

-- every prefix of a 3-AP-free set is a 3-AP-free subset of `[0, n)`
theorem below_le (l : List ℕ) (hnd : l.Nodup)
    (hfree : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, a + c = b + b → a = c) (n : ℕ) :
    below l n ≤ SqueezeBench.Roth.f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hnil : l.filter (fun x => decide (x < 0)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a _
      simp
    have h0 : below l 0 = 0 := by simp only [below, hnil, List.length_nil]
    rw [h0]
    exact Nat.zero_le _
  · have hn1 : SqueezeBench.Roth.nMin ≤ n := by simp only [SqueezeBench.Roth.nMin_eq]; omega
    have hnd' : (l.filter (fun x => decide (x < n))).Nodup := hnd.filter _
    refine SqueezeBench.Roth.le_f_of_threeAPFree hn1
      (l.filter (fun x => decide (x < n))).toFinset ?_ ?_ ?_
    · intro a ha b hb c hc h
      have ha' := List.mem_filter.1 (List.mem_toFinset.1 (Finset.mem_coe.1 ha))
      have hb' := List.mem_filter.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hb))
      have hc' := List.mem_filter.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hc))
      have := hfree a ha'.1 b hb'.1 c hc'.1 h
      omega
    · intro x hx
      have := (List.mem_filter.1 (List.mem_toFinset.1 hx)).2
      simpa using this
    · rw [List.toFinset_card_of_nodup hnd']
      rfl

theorem setA_le (n : ℕ) : below setA n ≤ SqueezeBench.Roth.f n :=
  below_le setA (by decide) (free_of_all (by decide)) n

theorem setB_le (n : ℕ) : below setB n ≤ SqueezeBench.Roth.f n :=
  below_le setB (by decide) (free_of_all (by decide)) n

theorem tbl_le (n : ℕ) : tbl n ≤ SqueezeBench.Roth.f n :=
  max_le (max_le (setA_le n) (setB_le n)) (SqueezeBench.Roth.Lower.V003.cnt_valid n)

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
    · exact tbl_le n
    · rename_i h27
      have h₁ := ih ((n + 2) / 3) (by omega)
      have h₂ := ih ((n + 1) / 3) (by omega)
      have := SqueezeBench.Roth.Lower.V002.split_le n (by omega)
      omega

theorem cnt_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f cnt :=
  fun n => cntAux_le n n le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  maxWith_valid SqueezeBench.Roth.Lower.V003.valid cnt_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V003.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V003.record record :=
  maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 24) (by decide) (by decide)

end SqueezeBench.Roth.Lower.V004
