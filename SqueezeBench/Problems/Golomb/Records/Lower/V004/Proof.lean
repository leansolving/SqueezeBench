import SqueezeBench.Problems.Golomb.Records.Lower.V004.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V003.Proof

/-!
# Golomb lower-bound record V004 — validity

The sliding window of V001 with V003's boundary slack harvested on two nested blocks.
Write `N = L + v + 1` for the number of windows and `cnt s` for the marks in the window
ending at `s`. For blocks `A₁ ≤ A₂` at each end with weights `W₁, W₂`, the weight of the
window ending at `s` is `W₁ + W₂` on the innermost block (`s < A₁` or `N - A₁ ≤ s`) and
`W₂` on the outer one, so it suffices that `W₁ + W₂ ≤ slack K₁` and `W₂ ≤ slack K₂`, where
`slack K = (q − K)(q − K + 1)` is V003's available slack on a window holding at most `K`
marks. Everything else is V003's: `cap` for the local Sidon bound, `tangent'` for the
integrality step with slack, `blockLen_two` for `2 · K(K+1)/2 = K(K+1)`.

`win`, `cnt`, `sum_cnt`, `sum_choose_eq`, `sum_spread_le`, `tangent`, `two_choose_two`,
`div_le_of_mul_le` are V001's, `bnd`/`bnd_le` V002's, `cap`/`tangent'`/`blockLen`/
`blockLen_two` V003's; see `based-on`.
-/

namespace SqueezeBench.Golomb.Lower.V004

open SqueezeBench Finset
open SqueezeBench.Golomb.Lower.V001 (win cnt mem_win tangent two_choose_two div_le_of_mul_le
  sum_cnt sum_choose_eq sum_spread_le)
open SqueezeBench.Golomb.Lower.V003 (blockLen blockLen_two cap tangent')

/-! ## Two sums of block indicators -/

theorem sum_left (N A W : ℕ) (h : A ≤ N) :
    ∑ s ∈ range N, (if s < A then W else 0) = A * W := by
  rw [← Finset.sum_filter]
  have hfe : ((range N).filter (fun s => s < A)) = range A := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [hfe, Finset.sum_const, card_range, smul_eq_mul]

theorem sum_right (N A W : ℕ) (h : A ≤ N) :
    ∑ s ∈ range N, (if N - A ≤ s then W else 0) = A * W := by
  rw [← Finset.sum_filter]
  have hfe : ((range N).filter (fun s => N - A ≤ s)) = Finset.Ico (N - A) N := by
    ext s
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfe, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  congr 1
  omega

/-! ## The two-block master inequality -/

theorem master2 {m L : ℕ} (hL : L ∈ RulerLengths m) (q v A₁ A₂ K₁ K₂ W₁ W₂ : ℕ)
    (hA : A₁ ≤ A₂) (h2A : 2 * A₂ ≤ L)
    (hcap₁ : 2 * A₁ ≤ K₁ * (K₁ + 1)) (hcap₂ : 2 * A₂ ≤ K₂ * (K₂ + 1))
    (hW₁ : W₁ + W₂ ≤ (q - K₁) * (q - K₁ + 1)) (hW₂ : W₂ ≤ (q - K₂) * (q - K₂ + 1)) :
    2 * q * (v + 1) * m + 2 * (A₁ * W₁ + A₂ * W₂)
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
          + (((if s < A₁ then W₁ else 0) + (if s < A₂ then W₂ else 0))
            + ((if L + v + 1 - A₁ ≤ s then W₁ else 0)
              + (if L + v + 1 - A₂ ≤ s then W₂ else 0)))
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
    · have hn2 : ¬ (L + v + 1 - A₁ ≤ s) := by omega
      have hn3 : ¬ (L + v + 1 - A₂ ≤ s) := by omega
      have hcK : cnt S v s ≤ K₁ := hfromcap s K₁ hcapL (by omega)
      have := tangent' (cnt S v s) q K₁ hcK
      rw [if_pos h1, if_pos (show s < A₂ by omega), if_neg hn2, if_neg hn3]
      omega
    · by_cases h2 : s < A₂
      · have hn2 : ¬ (L + v + 1 - A₁ ≤ s) := by omega
        have hn3 : ¬ (L + v + 1 - A₂ ≤ s) := by omega
        have hcK : cnt S v s ≤ K₂ := hfromcap s K₂ hcapL (by omega)
        have := tangent' (cnt S v s) q K₂ hcK
        rw [if_neg h1, if_pos h2, if_neg hn2, if_neg hn3]
        omega
      · by_cases h3 : L + v + 1 - A₁ ≤ s
        · have hcK : cnt S v s ≤ K₁ := hfromcap (L + v - s) K₁ hcapR (by omega)
          have := tangent' (cnt S v s) q K₁ hcK
          rw [if_neg h1, if_neg h2, if_pos h3, if_pos (show L + v + 1 - A₂ ≤ s by omega)]
          omega
        · by_cases h4 : L + v + 1 - A₂ ≤ s
          · have hcK : cnt S v s ≤ K₂ := hfromcap (L + v - s) K₂ hcapR (by omega)
            have := tangent' (cnt S v s) q K₂ hcK
            rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
            omega
          · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
            have := tangent (cnt S v s) q
            omega
  have hgsum : ∑ s ∈ range (L + v + 1),
      (((if s < A₁ then W₁ else 0) + (if s < A₂ then W₂ else 0))
        + ((if L + v + 1 - A₁ ≤ s then W₁ else 0)
          + (if L + v + 1 - A₂ ≤ s then W₂ else 0)))
      = 2 * (A₁ * W₁ + A₂ * W₂) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_left (L + v + 1) A₁ W₁ (by omega), sum_left (L + v + 1) A₂ W₂ (by omega),
      sum_right (L + v + 1) A₁ W₁ (by omega), sum_right (L + v + 1) A₂ W₂ (by omega)]
    omega
  have e4 := Finset.sum_le_sum e3
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, hgsum, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, card_range, smul_eq_mul] at e4
  have heq : 2 * q * (v + 1) * m = 2 * q * (m * (v + 1)) := by ring
  rw [heq]
  omega

/-! ## The bound -/

/-- The slack is decreasing in the cap. -/
theorem slack_le {q K₁ K₂ : ℕ} (h : K₁ ≤ K₂) : slack q K₂ ≤ slack q K₁ :=
  Nat.mul_le_mul (by omega) (by omega)

theorem gbnd_le {m L : ℕ} (hL : L ∈ RulerLengths m) (q u K₁ K₂ : ℕ) : gbnd m q u K₁ K₂ ≤ L := by
  rw [gbnd]
  split
  · rename_i hg
    obtain ⟨hq, hu, hK, hAL⟩ := hg
    have h2A : 2 * blockLen K₂ ≤ L :=
      le_trans hAL (SqueezeBench.Golomb.Lower.V002.bnd_le hL q u)
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have hbl : blockLen K₁ ≤ blockLen K₂ := by
      rw [blockLen, blockLen]
      exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    have hsl : slack q K₂ ≤ slack q K₁ := slack_le (by omega)
    have hmas := master2 hL q v (blockLen K₁) (blockLen K₂) K₁ K₂
      (slack q K₁ - slack q K₂) (slack q K₂) hbl h2A
      (le_of_eq (blockLen_two K₁)) (le_of_eq (blockLen_two K₂))
      (by simp only [slack] at hsl ⊢; omega) (le_of_eq rfl)
    have hqq : 0 < q * (q + 1) := Nat.mul_pos hq (by omega)
    have key : 2 * q * (v + 1) * m + gain q K₁ K₂ - (v + 1 - 1) * (v + 1)
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
  all_goals exact gbnd_le hL _ _ _ _

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  maxWith_valid SqueezeBench.Golomb.Lower.V003.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V003.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V003.record record :=
  maxWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 12) (by decide) (by decide)

end SqueezeBench.Golomb.Lower.V004
