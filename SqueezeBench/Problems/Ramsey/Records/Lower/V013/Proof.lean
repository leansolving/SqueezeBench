import SqueezeBench.Problems.Ramsey.Records.Lower.V013.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V012.Proof

/-! Record V013 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V013.lean`. No new mathematics: the exact binomial coefficients
replace the power bounds `C(N,k) ≤ N^k/k!` in the records of V007 (alteration) and V012
(Spencer). The record's `binom` is Mathlib's `Nat.choose` by `Nat.choose_succ_right_eq`;
the Spencer scan keeps V012's exact condition invariant, and its result feeds
`V012.not_forces` directly; the alteration window evaluates the exact deletion bound
`N − ⌊2·C(N,n)/2^C(n,2)⌋`, valid at every `N` by V007's `exists_few` and `not_forces_alt`. -/

namespace SqueezeBench.Ramsey.Lower.V013

open SqueezeBench SimpleGraph Finset

theorem binom_eq (N : ℕ) : ∀ k, binom N k = N.choose k
  | 0 => by simp [binom]
  | k + 1 => by
    rw [binom, binom_eq N k, ← Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (Nat.succ_pos k)

/-! ## Spencer's bound with the exact binomial -/

theorem okS_iff {n N : ℕ} : okS n N = true ↔
    2 * (n.choose 2 * (N - 2).choose (n - 2) + 1) * 2718281829 ≤ 2 ^ n.choose 2 * 10 ^ 9 := by
  simp only [okS, binom_eq, Nat.choose_two_right, decide_eq_true_eq]

theorem scanS_ok {n : ℕ} : ∀ fuel N, okS n N = true → okS n (scanS n fuel N) = true := by
  intro fuel
  induction fuel with
  | zero => intro N h; simpa [scanS] using h
  | succ fuel ih =>
    intro N h
    rw [scanS]
    split_ifs with h1
    · exact ih _ h1
    · exact h

-- V012's power-bound condition implies the exact one.
theorem spencer_okS {n : ℕ} (hn3 : 3 ≤ n) : okS n (V012.spencer n) = true := by
  rw [okS_iff]
  have hM := V012.spencer_ok hn3
  have h1 : (n - 2).factorial * (V012.spencer n - 2).choose (n - 2) ≤
      (V012.spencer n - 2) ^ (n - 2) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have h3 : (n - 2).factorial *
      (2 * (n.choose 2 * (V012.spencer n - 2).choose (n - 2) + 1) * 2718281829) ≤
      (n - 2).factorial * (2 ^ n.choose 2 * 10 ^ 9) := by
    calc (n - 2).factorial *
          (2 * (n.choose 2 * (V012.spencer n - 2).choose (n - 2) + 1) * 2718281829)
        = 2 * (n.choose 2 * ((n - 2).factorial * (V012.spencer n - 2).choose (n - 2)) +
            (n - 2).factorial) * 2718281829 := by ring
      _ ≤ 2 * (n.choose 2 * (V012.spencer n - 2) ^ (n - 2) + (n - 2).factorial) *
            2718281829 := by gcongr
      _ ≤ 2 ^ n.choose 2 * (n - 2).factorial * 10 ^ 9 := hM
      _ = (n - 2).factorial * (2 ^ n.choose 2 * 10 ^ 9) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (Nat.factorial_pos _)

theorem spencerE_le {n : ℕ} (hn3 : 3 ≤ n) : spencerE n + 1 ≤ f n := by
  have hok : okS n (spencerE n) = true := scanS_ok 200 _ (spencer_okS hn3)
  rw [okS_iff] at hok
  have hn : nMin ≤ n := by simp [nMin]; omega
  refine le_f hn ?_
  intro N hN
  by_contra hcon
  have hNM : N ≤ spencerE n := by omega
  rcases Nat.lt_or_ge N n with hlt | hge
  · exact V012.not_forces_small (by omega) hlt hN
  · refine V012.not_forces hn3 hge ?_ hN
    have h1 : (N - 2).choose (n - 2) ≤ (spencerE n - 2).choose (n - 2) :=
      Nat.choose_le_choose _ (Nat.sub_le_sub_right hNM 2)
    calc 2 * (n.choose 2 * (N - 2).choose (n - 2) + 1) * 2718281829
        ≤ 2 * (n.choose 2 * (spencerE n - 2).choose (n - 2) + 1) * 2718281829 := by gcongr
      _ ≤ 2 ^ n.choose 2 * 10 ^ 9 := hok

/-! ## The alteration bound with the exact binomial -/

theorem alt_exact_le {n N : ℕ} (hn2 : 2 ≤ n) :
    N - 2 * N.choose n / 2 ^ n.choose 2 + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro M hM
  by_contra hcon
  have hMd : M ≤ N - 2 * N.choose n / 2 ^ n.choose 2 := by omega
  have hKpos : 0 < 2 ^ n.choose 2 := by positivity
  have hd : 2 * N.choose n < (2 * N.choose n / 2 ^ n.choose 2 + 1) * 2 ^ n.choose 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add hKpos
  obtain ⟨c, hc⟩ := V007.exists_few hd
  exact V007.not_forces_alt (by omega) c hc hMd hM

theorem gA_le {n : ℕ} (hn2 : 2 ≤ n) (N : ℕ) : gA n N + 1 ≤ f n := by
  unfold gA
  rw [binom_eq, ← Nat.choose_two_right]
  exact alt_exact_le hn2

theorem scanA_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel N best,
    best + 1 ≤ f n → scanA n fuel N best + 1 ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro N best h; simpa [scanA] using h
  | succ fuel ih =>
    intro N best h
    rw [scanA]
    refine ih _ _ ?_
    rcases Nat.le_total best (gA n N) with h1 | h1
    · rw [Nat.max_eq_right h1]; exact gA_le hn2 N
    · rw [Nat.max_eq_left h1]; exact h

theorem altE_le {n : ℕ} (hn2 : 2 ≤ n) : altE n + 1 ≤ f n :=
  scanA_le hn2 40 _ 0 (V008.one_le hn2)

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by omega
  rcases Nat.le_total (spencerE n) (altE n) with h | h
  · rw [Nat.max_eq_right h]; exact altE_le hn2
  · rw [Nat.max_eq_left h]; exact spencerE_le hn

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V012.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V012.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V012.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 14) (by decide)
    (by decide +kernel)

end SqueezeBench.Ramsey.Lower.V013
