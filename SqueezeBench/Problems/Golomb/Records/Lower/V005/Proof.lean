import SqueezeBench.Problems.Golomb.Records.Lower.V005.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V004.Proof

/-!
# Golomb lower-bound record V005 — validity

V004's argument with a third nested block. The window ending at `s` is credited
`∑_{i : s < A_i} W_i`, which the telescoping weights make equal to `slack q K_i` on the
`i`-th block, exactly the slack that the local Sidon cap `cnt s ≤ K_i` provides there.
`master3` states the inequality for arbitrary `A₁ ≤ A₂ ≤ A₃`, `K₁ < K₂ < K₃` and weights
satisfying the three partial-sum conditions.

`sum_left`, `sum_right` and `slack` are V004's, `cap`/`tangent'`/`blockLen`/`blockLen_two`
V003's, `bnd_le` V002's, the window machinery V001's; see `based-on`.
-/

namespace SqueezeBench.Golomb.Lower.V005

open SqueezeBench Finset
open SqueezeBench.Golomb.Lower.V001 (win cnt mem_win tangent two_choose_two div_le_of_mul_le
  sum_cnt sum_choose_eq sum_spread_le)
open SqueezeBench.Golomb.Lower.V003 (blockLen blockLen_two cap tangent')
open SqueezeBench.Golomb.Lower.V004 (slack slack_le sum_left sum_right)

theorem master3 {m L : ℕ} (hL : L ∈ RulerLengths m) (q v A₁ A₂ A₃ K₁ K₂ K₃ W₁ W₂ W₃ : ℕ)
    (hA : A₁ ≤ A₂) (hA' : A₂ ≤ A₃) (h2A : 2 * A₃ ≤ L)
    (hcap₁ : 2 * A₁ ≤ K₁ * (K₁ + 1)) (hcap₂ : 2 * A₂ ≤ K₂ * (K₂ + 1))
    (hcap₃ : 2 * A₃ ≤ K₃ * (K₃ + 1))
    (hW₁ : W₁ + W₂ + W₃ ≤ (q - K₁) * (q - K₁ + 1))
    (hW₂ : W₂ + W₃ ≤ (q - K₂) * (q - K₂ + 1))
    (hW₃ : W₃ ≤ (q - K₃) * (q - K₃ + 1)) :
    2 * q * (v + 1) * m + 2 * (A₁ * W₁ + A₂ * W₂ + A₃ * W₃)
      ≤ (L + v + 1) * (q * (q + 1)) + v * (v + 1) := by
  obtain ⟨S, hsub, hcard, hsid, _⟩ := hL
  have hS : ∀ a ∈ S, a ≤ L := by
    intro a ha
    have := hsub ha
    rw [mem_range] at this
    omega
  have e1 : ∑ s ∈ range (L + v + 1), cnt S v s = m * (v + 1) := by
    rw [sum_cnt hS, hcard]
  have e2 : 2 * ∑ s ∈ range (L + v + 1), (cnt S v s).choose 2 ≤ v * (v + 1) := by
    rw [sum_choose_eq hS]
    exact sum_spread_le v hsid
  have e3 : ∀ s ∈ range (L + v + 1),
      2 * q * cnt S v s
          + ((((if s < A₁ then W₁ else 0) + (if s < A₂ then W₂ else 0))
              + (if s < A₃ then W₃ else 0))
            + (((if L + v + 1 - A₁ ≤ s then W₁ else 0)
                + (if L + v + 1 - A₂ ≤ s then W₂ else 0))
              + (if L + v + 1 - A₃ ≤ s then W₃ else 0)))
        ≤ 2 * (cnt S v s).choose 2 + q * (q + 1) := by
    intro s hs
    rw [mem_range] at hs
    have hct := two_choose_two (cnt S v s)
    have hfromcap : ∀ D K, (cnt S v s).choose 2 ≤ D → 2 * D < K * (K + 1) →
        cnt S v s ≤ K := by
      intro D K hD hDK
      by_contra hgt
      have h1 : K + 1 ≤ cnt S v s := by omega
      have hmul : K * (K + 1) ≤ cnt S v s * (cnt S v s - 1) := by
        calc K * (K + 1) = (K + 1) * K := by ring
          _ ≤ cnt S v s * (cnt S v s - 1) := Nat.mul_le_mul h1 (by omega)
      omega
    have hcapL : (cnt S v s).choose 2 ≤ s :=
      cap hsid (by
        intro a ha b hb hab
        rw [mem_win] at ha hb
        omega)
    have hcapR : (cnt S v s).choose 2 ≤ L + v - s :=
      cap hsid (by
        intro a ha b hb hab
        rw [mem_win] at ha hb
        have := hS b hb.1
        omega)
    by_cases h1 : s < A₁
    · have hcK : cnt S v s ≤ K₁ := hfromcap s K₁ hcapL (by omega)
      have := tangent' (cnt S v s) q K₁ hcK
      rw [if_pos h1, if_pos (show s < A₂ by omega), if_pos (show s < A₃ by omega),
        if_neg (show ¬ (L + v + 1 - A₁ ≤ s) by omega),
        if_neg (show ¬ (L + v + 1 - A₂ ≤ s) by omega),
        if_neg (show ¬ (L + v + 1 - A₃ ≤ s) by omega)]
      omega
    · by_cases h2 : s < A₂
      · have hcK : cnt S v s ≤ K₂ := hfromcap s K₂ hcapL (by omega)
        have := tangent' (cnt S v s) q K₂ hcK
        rw [if_neg h1, if_pos h2, if_pos (show s < A₃ by omega),
          if_neg (show ¬ (L + v + 1 - A₁ ≤ s) by omega),
          if_neg (show ¬ (L + v + 1 - A₂ ≤ s) by omega),
          if_neg (show ¬ (L + v + 1 - A₃ ≤ s) by omega)]
        omega
      · by_cases h3 : s < A₃
        · have hcK : cnt S v s ≤ K₃ := hfromcap s K₃ hcapL (by omega)
          have := tangent' (cnt S v s) q K₃ hcK
          rw [if_neg h1, if_neg h2, if_pos h3,
            if_neg (show ¬ (L + v + 1 - A₁ ≤ s) by omega),
            if_neg (show ¬ (L + v + 1 - A₂ ≤ s) by omega),
            if_neg (show ¬ (L + v + 1 - A₃ ≤ s) by omega)]
          omega
        · by_cases h4 : L + v + 1 - A₁ ≤ s
          · have hcK : cnt S v s ≤ K₁ := hfromcap (L + v - s) K₁ hcapR (by omega)
            have := tangent' (cnt S v s) q K₁ hcK
            rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4,
              if_pos (show L + v + 1 - A₂ ≤ s by omega),
              if_pos (show L + v + 1 - A₃ ≤ s by omega)]
            omega
          · by_cases h5 : L + v + 1 - A₂ ≤ s
            · have hcK : cnt S v s ≤ K₂ := hfromcap (L + v - s) K₂ hcapR (by omega)
              have := tangent' (cnt S v s) q K₂ hcK
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5,
                if_pos (show L + v + 1 - A₃ ≤ s by omega)]
              omega
            · by_cases h6 : L + v + 1 - A₃ ≤ s
              · have hcK : cnt S v s ≤ K₃ := hfromcap (L + v - s) K₃ hcapR (by omega)
                have := tangent' (cnt S v s) q K₃ hcK
                rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
                omega
              · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]
                have := tangent (cnt S v s) q
                omega
  have hgsum : ∑ s ∈ range (L + v + 1),
      ((((if s < A₁ then W₁ else 0) + (if s < A₂ then W₂ else 0))
          + (if s < A₃ then W₃ else 0))
        + (((if L + v + 1 - A₁ ≤ s then W₁ else 0)
            + (if L + v + 1 - A₂ ≤ s then W₂ else 0))
          + (if L + v + 1 - A₃ ≤ s then W₃ else 0)))
      = 2 * (A₁ * W₁ + A₂ * W₂ + A₃ * W₃) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_left (L + v + 1) A₁ W₁ (by omega), sum_left (L + v + 1) A₂ W₂ (by omega),
      sum_left (L + v + 1) A₃ W₃ (by omega),
      sum_right (L + v + 1) A₁ W₁ (by omega), sum_right (L + v + 1) A₂ W₂ (by omega),
      sum_right (L + v + 1) A₃ W₃ (by omega)]
    omega
  have e4 := Finset.sum_le_sum e3
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, hgsum, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, card_range, smul_eq_mul] at e4
  have heq : 2 * q * (v + 1) * m = 2 * q * (m * (v + 1)) := by ring
  rw [heq]
  omega

theorem gbnd_le {m L : ℕ} (hL : L ∈ RulerLengths m) (q u K₁ K₂ K₃ : ℕ) :
    gbnd m q u K₁ K₂ K₃ ≤ L := by
  rw [gbnd]
  split
  · rename_i hg
    obtain ⟨hq, hu, hK, hK', hAL⟩ := hg
    have h2A : 2 * blockLen K₃ ≤ L :=
      le_trans hAL (SqueezeBench.Golomb.Lower.V002.bnd_le hL q u)
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have hbl : blockLen K₁ ≤ blockLen K₂ := by
      rw [blockLen, blockLen]
      exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    have hbl' : blockLen K₂ ≤ blockLen K₃ := by
      rw [blockLen, blockLen]
      exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    have hsl : slack q K₂ ≤ slack q K₁ := slack_le (by omega)
    have hsl' : slack q K₃ ≤ slack q K₂ := slack_le (by omega)
    have hmas := master3 hL q v (blockLen K₁) (blockLen K₂) (blockLen K₃) K₁ K₂ K₃
      (slack q K₁ - slack q K₂) (slack q K₂ - slack q K₃) (slack q K₃) hbl hbl' h2A
      (le_of_eq (blockLen_two K₁)) (le_of_eq (blockLen_two K₂)) (le_of_eq (blockLen_two K₃))
      (by simp only [slack] at hsl hsl' ⊢; omega)
      (by simp only [slack] at hsl' ⊢; omega) (le_of_eq rfl)
    have hqq : 0 < q * (q + 1) := Nat.mul_pos hq (by omega)
    have key : 2 * q * (v + 1) * m + gain q K₁ K₂ K₃ - (v + 1 - 1) * (v + 1)
        ≤ (L + v + 1) * (q * (q + 1)) := by
      simp only [Nat.add_sub_cancel]
      rw [gain]
      omega
    have h1 := div_le_of_mul_le hqq key
    omega
  · exact Nat.zero_le L

theorem w_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f w := by
  refine pin_lowerBoundHolds ?_
  intro m hm
  refine le_f hm ?_
  intro L hL
  show wRaw m ≤ L
  simp only [wRaw, bestU, bestK]
  repeat' apply max_le
  all_goals exact gbnd_le hL _ _ _ _ _

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  maxWith_valid SqueezeBench.Golomb.Lower.V004.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V004.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V004.record record :=
  maxWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 18) (by decide) (by decide)

end SqueezeBench.Golomb.Lower.V005
