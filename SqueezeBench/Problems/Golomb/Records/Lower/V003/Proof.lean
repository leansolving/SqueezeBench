import SqueezeBench.Problems.Golomb.Records.Lower.V003.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V002.Proof

/-!
# Golomb lower-bound record V003 — validity

V001's sliding window, with the boundary windows counted better. Write `cnt s` for the
number of marks in the window of length `u = v + 1` ending at `s`, over the `L + v + 1`
windows that can meet a mark.

* `∑ cnt s = m * (v + 1)` and `2 * ∑ C(cnt s, 2) ≤ v * (v + 1)` are V001's.
* **New:** the window ending at `s` sees only `[0, s]`, so the distances of its pairs of
  marks are distinct elements of `[1, s]` and `C(cnt s, 2) ≤ s`. Symmetrically it sees only
  `[s - v, L]`, so `C(cnt s, 2) ≤ L + v - s`. Hence `cnt s ≤ K` as soon as
  `2 * K * (K + 1) / 2 ≤ K * (K + 1)` bounds twice the local budget, which holds on the
  first and last `A = K * (K + 1) / 2` windows.
* On those `2 * A` windows the tangent estimate has slack
  `(q - cnt s) * (q - cnt s + 1) ≥ (q - K) * (q - K + 1)`.

Summing gives the improved master inequality

`2 * q * (v+1) * m + 2 * A * (q - K) * (q - K + 1) ≤ (L + v + 1) * q * (q+1) + v * (v+1)`,

valid whenever `2 * A ≤ L`, which the record's guard secures through V002's `bnd`.

`win`, `cnt`, `sum_cnt`, `sum_choose_eq`, `sum_spread_le`, `spread_injOn`, `tangent`,
`two_choose_two` and `div_le_of_mul_le` are V001's, `spread` and `exists_pair` V000's,
`bnd_le` V002's; see `based-on`.
-/

namespace SqueezeBench.Golomb.Lower.V003

open SqueezeBench Finset
open SqueezeBench.Golomb.Lower.V000 (spread spread_pair exists_pair)
open SqueezeBench.Golomb.Lower.V001 (win cnt mem_win win_subset spread_injOn tangent
  two_choose_two div_le_of_mul_le sum_cnt sum_choose_eq sum_spread_le)

/-! ## The local Sidon cap -/

/-- If every pair of marks of a window has distance at most `D`, the window holds at most
`D` pairs: the distances are distinct elements of `[1, D]`. -/
theorem cap {S : Finset ℕ} (hsid : IsSidon S) {v s D : ℕ}
    (h : ∀ a ∈ win S v s, ∀ b ∈ win S v s, a < b → b - a ≤ D) :
    (cnt S v s).choose 2 ≤ D := by
  have hmaps : ∀ T ∈ (win S v s).powersetCard 2, spread T ∈ Finset.Icc 1 D := by
    intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨a, b, hab, rfl⟩ := exists_pair hT.2
    have ha : a ∈ win S v s := hT.1 (by simp)
    have hb : b ∈ win S v s := hT.1 (by simp)
    have := h a ha b hb hab
    rw [spread_pair hab, mem_Icc]
    omega
  have hinj : Set.InjOn spread ((win S v s).powersetCard 2) := by
    intro T hT T' hT' heq
    rw [mem_coe, mem_powersetCard] at hT hT'
    refine spread_injOn hsid T ?_ T' ?_ heq
    · rw [mem_powersetCard]; exact ⟨hT.1.trans (win_subset S v s), hT.2⟩
    · rw [mem_powersetCard]; exact ⟨hT'.1.trans (win_subset S v s), hT'.2⟩
  have hle := Finset.card_le_card_of_injOn spread hmaps hinj
  rw [card_powersetCard, Nat.card_Icc] at hle
  have hc : cnt S v s = (win S v s).card := rfl
  rw [hc]
  omega

/-- The tangent estimate with the slack of a window known to hold at most `K` marks. -/
theorem tangent' (c q K : ℕ) (hc : c ≤ K) :
    2 * q * c + (q - K) * (q - K + 1) ≤ c * (c - 1) + q * (q + 1) := by
  rcases Nat.le_total q K with h | h
  · have h0 : q - K = 0 := by omega
    rw [h0]
    have := tangent c q
    omega
  · obtain ⟨p, rfl⟩ : ∃ p, q = K + p := ⟨q - K, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, K = c + r := ⟨K - c, by omega⟩
    have h0 : c + r + p - (c + r) = p := by omega
    rw [h0]
    rcases c with _ | d
    · simp; nlinarith
    · simp only [Nat.succ_sub_one]
      nlinarith

/-! ## The improved master inequality -/

theorem master' {m L : ℕ} (hL : L ∈ RulerLengths m) (q v A K : ℕ)
    (hcap : 2 * A ≤ K * (K + 1)) (h2A : 2 * A ≤ L) :
    2 * q * (v + 1) * m + 2 * (A * ((q - K) * (q - K + 1)))
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
          + ((if s < A then (q - K) * (q - K + 1) else 0)
            + (if L + v + 1 - A ≤ s then (q - K) * (q - K + 1) else 0))
        ≤ 2 * (cnt S v s).choose 2 + q * (q + 1) := by
    intro s hs
    rw [mem_range] at hs
    have hct := two_choose_two (cnt S v s)
    have hfromcap : ∀ D, (cnt S v s).choose 2 ≤ D → 2 * D < K * (K + 1) →
        cnt S v s ≤ K := by
      intro D hD hDK
      by_contra hgt
      have h1 : K + 1 ≤ cnt S v s := by omega
      have hmul : K * (K + 1) ≤ cnt S v s * (cnt S v s - 1) := by
        calc K * (K + 1) = (K + 1) * K := by ring
          _ ≤ cnt S v s * (cnt S v s - 1) := Nat.mul_le_mul h1 (by omega)
      omega
    by_cases h1 : s < A
    · have hne : ¬ (L + v + 1 - A ≤ s) := by omega
      have hcapL : (cnt S v s).choose 2 ≤ s :=
        cap hsid (by
          intro a ha b hb hab
          rw [mem_win] at ha hb
          omega)
      have hcK : cnt S v s ≤ K := hfromcap s hcapL (by omega)
      have := tangent' (cnt S v s) q K hcK
      rw [if_pos h1, if_neg hne]
      omega
    · by_cases h2 : L + v + 1 - A ≤ s
      · have hcapR : (cnt S v s).choose 2 ≤ L + v - s :=
          cap hsid (by
            intro a ha b hb hab
            rw [mem_win] at ha hb
            have := hS b hb.1
            omega)
        have hcK : cnt S v s ≤ K := hfromcap (L + v - s) hcapR (by omega)
        have := tangent' (cnt S v s) q K hcK
        rw [if_neg h1, if_pos h2]
        omega
      · rw [if_neg h1, if_neg h2]
        have := tangent (cnt S v s) q
        omega
  have hgsum : ∑ s ∈ range (L + v + 1),
      ((if s < A then (q - K) * (q - K + 1) else 0)
        + (if L + v + 1 - A ≤ s then (q - K) * (q - K + 1) else 0))
      = 2 * (A * ((q - K) * (q - K + 1))) := by
    rw [Finset.sum_add_distrib]
    have hl : ∑ s ∈ range (L + v + 1), (if s < A then (q - K) * (q - K + 1) else 0)
        = A * ((q - K) * (q - K + 1)) := by
      rw [← Finset.sum_filter]
      have hfe : ((range (L + v + 1)).filter (fun s => s < A)) = range A := by
        ext s
        simp only [mem_filter, mem_range]
        omega
      rw [hfe, Finset.sum_const, card_range, smul_eq_mul]
    have hr : ∑ s ∈ range (L + v + 1), (if L + v + 1 - A ≤ s then (q - K) * (q - K + 1) else 0)
        = A * ((q - K) * (q - K + 1)) := by
      rw [← Finset.sum_filter]
      have hfe : ((range (L + v + 1)).filter (fun s => L + v + 1 - A ≤ s))
          = Finset.Ico (L + v + 1 - A) (L + v + 1) := by
        ext s
        simp only [mem_filter, mem_range, mem_Ico]
        omega
      rw [hfe, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      congr 1
      omega
    rw [hl, hr]
    omega
  have e4 := Finset.sum_le_sum e3
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, hgsum, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, card_range, smul_eq_mul] at e4
  have heq : 2 * q * (v + 1) * m = 2 * q * (m * (v + 1)) := by ring
  rw [heq]
  omega

/-! ## The bound -/

theorem blockLen_two (K : ℕ) : 2 * blockLen K = K * (K + 1) := by
  obtain ⟨r, hr⟩ := Nat.even_mul_succ_self K
  have h : K * (K + 1) = r + r := hr
  rw [blockLen, h]
  omega

theorem gbnd_le {m L : ℕ} (hL : L ∈ RulerLengths m) (q u K : ℕ) : gbnd m q u K ≤ L := by
  rw [gbnd]
  split
  · rename_i hg
    obtain ⟨hq, hu, hAL⟩ := hg
    have h2A : 2 * blockLen K ≤ L := le_trans hAL (SqueezeBench.Golomb.Lower.V002.bnd_le hL q u)
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have hcap : 2 * blockLen K ≤ K * (K + 1) := le_of_eq (blockLen_two K)
    have hmas := master' hL q v (blockLen K) K hcap h2A
    have hgain : blockGain q K = 2 * (blockLen K * ((q - K) * (q - K + 1))) := by
      rw [blockGain, ← blockLen_two K]
      ring
    have hqq : 0 < q * (q + 1) := Nat.mul_pos hq (by omega)
    have key : 2 * q * (v + 1) * m + blockGain q K - (v + 1 - 1) * (v + 1)
        ≤ (L + v + 1) * (q * (q + 1)) := by
      simp only [Nat.add_sub_cancel]
      rw [hgain]
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
  simp only [wRaw, bestK, bestU]
  repeat' apply max_le
  all_goals exact gbnd_le hL _ _ _

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  maxWith_valid SqueezeBench.Golomb.Lower.V002.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V002.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V002.record record :=
  maxWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 8) (by decide) (by decide)

end SqueezeBench.Golomb.Lower.V003
