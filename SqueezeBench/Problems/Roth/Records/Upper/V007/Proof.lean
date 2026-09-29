import SqueezeBench.Problems.Roth.Records.Upper.V007.Def
import SqueezeBench.Problems.Roth.Records.Upper.V006.Proof

/-! Record V007 for Roth, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V007.lean`. -/

namespace SqueezeBench.Roth.Upper.V007

open SqueezeBench.Roth.Upper.V006 (NewQ Dt mem_Dt)
open SqueezeBench.Roth.Upper.V005 (hle_of_mono)

/-! ### Moser's two choices, for enumerations of any length

`[ij]` is `a (i-1) + a (j-1)`. One of `[14], [15]` and one of `[25], [26]` is no sum of two
of `a 2, a 3, …` (all of them, not only up to `a 6`): sums with an index `≥ 5`, resp. `≥ 6`,
are too large to coincide. -/

theorem u_gen (t : ℕ) (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < t → a i < a j)
    (hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) (ht : 5 ≤ t) :
    ∃ u, (u = a 0 + a 3 ∨ u = a 0 + a 4) ∧ NewQ a u ∧
      ∀ p q, 2 ≤ p → p < q → q < t → u ≠ a p + a q := by
  have h01 := hmono 0 1 (by norm_num) (by omega)
  have h12 := hmono 1 2 (by norm_num) (by omega)
  have h23 := hmono 2 3 (by norm_num) (by omega)
  have h34 := hmono 3 4 (by norm_num) (by omega)
  have hle := hle_of_mono hmono
  -- sums with an index `≥ 5` exceed `[15]`
  have big : ∀ x, x ≤ a 0 + a 4 → ∀ p q, 2 ≤ p → p < q → q < t → 5 ≤ q → x ≠ a p + a q := by
    intro x hx p q hp hpq hq hq5
    have := hle 2 p hp (by omega)
    have := hmono 4 q (by omega) hq
    omega
  by_cases h : a 0 + a 3 = a 1 + a 2
  · refine ⟨a 0 + a 4, Or.inr rfl, ⟨by omega, by omega, by omega, ?_⟩, ?_⟩
    · intro e
      exact absurd (hfree 2 3 4 (by omega) (by omega) (by omega) (by omega)) (by decide)
    · intro p q hp hpq hq
      by_cases hq5 : 5 ≤ q
      · exact big _ le_rfl p q hp hpq hq hq5
      · have hp4 : p < 4 := by omega
        interval_cases p <;> interval_cases q
        · intro e
          exact absurd (hfree 1 3 4 (by omega) (by omega) (by omega) (by omega)) (by decide)
        all_goals omega
  · refine ⟨a 0 + a 3, Or.inl rfl, ⟨by omega, by omega, h, by omega⟩, ?_⟩
    intro p q hp hpq hq
    by_cases hq5 : 5 ≤ q
    · exact big _ (by omega) p q hp hpq hq hq5
    · have hp4 : p < 4 := by omega
      interval_cases p <;> interval_cases q <;> omega

theorem v_gen (t : ℕ) (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < t → a i < a j)
    (hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) (ht : 6 ≤ t) :
    ∃ v, (v = a 1 + a 4 ∨ v = a 1 + a 5) ∧ NewQ a v ∧
      ∀ p q, 2 ≤ p → p < q → q < t → v ≠ a p + a q := by
  have h01 := hmono 0 1 (by norm_num) (by omega)
  have h12 := hmono 1 2 (by norm_num) (by omega)
  have h23 := hmono 2 3 (by norm_num) (by omega)
  have h34 := hmono 3 4 (by norm_num) (by omega)
  have h45 := hmono 4 5 (by norm_num) (by omega)
  have hle := hle_of_mono hmono
  have big : ∀ x, x ≤ a 1 + a 5 → ∀ p q, 2 ≤ p → p < q → q < t → 6 ≤ q → x ≠ a p + a q := by
    intro x hx p q hp hpq hq hq6
    have := hle 2 p hp (by omega)
    have := hmono 5 q (by omega) hq
    omega
  by_cases h : a 1 + a 4 = a 2 + a 3
  · refine ⟨a 1 + a 5, Or.inr rfl, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro p q hp hpq hq
    by_cases hq6 : 6 ≤ q
    · exact big _ le_rfl p q hp hpq hq hq6
    · have hp5 : p < 5 := by omega
      interval_cases p <;> interval_cases q
      · omega
      · intro e
        exact absurd (hfree 3 4 5 (by omega) (by omega) (by omega) (by omega)) (by decide)
      · omega
      · intro e
        exact absurd (hfree 2 4 5 (by omega) (by omega) (by omega) (by omega)) (by decide)
      all_goals omega
  · refine ⟨a 1 + a 4, Or.inl rfl, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro p q hp hpq hq
    by_cases hq6 : 6 ≤ q
    · exact big _ (by omega) p q hp hpq hq hq6
    · have hp5 : p < 5 := by omega
      interval_cases p <;> interval_cases q <;> omega

/-! ### The base cases `|A +̂ A| ≥ 9` (`t = 5`) and `|A +̂ A| ≥ 12` (`t = 6`) -/

-- Nine sums of five elements: `[12], [13], [23], [24]`, two of `[14], [15], [25]`, and
-- `[34], [35], [45]`. If `[25] = [34]` then `[14]` and `[15]` are both new, else `[25]` is.
theorem five_base (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < 5 → a i < a j)
    (hfree : ∀ i j k, i < 5 → j < 5 → k < 5 → a i + a k = a j + a j → i = j) :
    9 ≤ (Dt 5 a).card := by
  have h01 := hmono 0 1 (by norm_num) (by norm_num)
  have h12 := hmono 1 2 (by norm_num) (by norm_num)
  have h23 := hmono 2 3 (by norm_num) (by norm_num)
  have h34 := hmono 3 4 (by norm_num) (by norm_num)
  -- a nine-element subset, given two new sums `x < y` among `[14], [15], [25]`
  have build : ∀ x y : ℕ, x < y → (∃ i j, i < 2 ∧ i < j ∧ j < 5 ∧ x = a i + a j) →
      (∃ i j, i < 2 ∧ i < j ∧ j < 5 ∧ y = a i + a j) →
      NewQ a x → NewQ a y → (∀ p q, 2 ≤ p → p < q → q < 5 → x ≠ a p + a q) →
      (∀ p q, 2 ≤ p → p < q → q < 5 → y ≠ a p + a q) → 9 ≤ (Dt 5 a).card := by
    intro x y hxy hx hy hxQ hyQ hxR hyR
    obtain ⟨x1, x2, x3, x4⟩ := hxQ
    obtain ⟨y1, y2, y3, y4⟩ := hyQ
    have hx1 := hxR 2 3 (by norm_num) (by norm_num) (by norm_num)
    have hx2 := hxR 2 4 (by norm_num) (by norm_num) (by norm_num)
    have hx3 := hxR 3 4 (by norm_num) (by norm_num) (by norm_num)
    have hy1 := hyR 2 3 (by norm_num) (by norm_num) (by norm_num)
    have hy2 := hyR 2 4 (by norm_num) (by norm_num) (by norm_num)
    have hy3 := hyR 3 4 (by norm_num) (by norm_num) (by norm_num)
    have hsub : ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3, x, y, a 2 + a 3, a 2 + a 4, a 3 + a 4} :
        Finset ℕ) ⊆ Dt 5 a := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [mem_Dt]
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, 1, by norm_num, by norm_num, rfl⟩
      · exact ⟨0, 2, by norm_num, by norm_num, rfl⟩
      · exact ⟨1, 2, by norm_num, by norm_num, rfl⟩
      · exact ⟨1, 3, by norm_num, by norm_num, rfl⟩
      · obtain ⟨i, j, _, hij, hj, rfl⟩ := hx; exact ⟨i, j, hij, hj, rfl⟩
      · obtain ⟨i, j, _, hij, hj, rfl⟩ := hy; exact ⟨i, j, hij, hj, rfl⟩
      · exact ⟨2, 3, by norm_num, by norm_num, rfl⟩
      · exact ⟨2, 4, by norm_num, by norm_num, rfl⟩
      · exact ⟨3, 4, by norm_num, by norm_num, rfl⟩
    refine le_trans (le_of_eq ?_) (Finset.card_le_card hsub)
    symm
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    · omega
    · exact ⟨by omega, by omega⟩
    · exact ⟨hy1, hy2, hy3⟩
    · exact ⟨hxy.ne, hx1, hx2, hx3⟩
    · exact ⟨fun e => x4 e.symm, fun e => y4 e.symm, by omega, by omega, by omega⟩
    · exact ⟨by omega, fun e => x3 e.symm, fun e => y3 e.symm, by omega, by omega, by omega⟩
    · exact ⟨by omega, by omega, fun e => x2 e.symm, fun e => y2 e.symm, by omega, by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega, fun e => x1 e.symm, fun e => y1 e.symm, by omega, by omega,
        by omega⟩
  by_cases h : a 1 + a 4 = a 2 + a 3
  · -- `[25] = [34]`: both `[14]` and `[15]` are new
    refine build (a 0 + a 3) (a 0 + a 4) (by omega)
      ⟨0, 3, by norm_num, by norm_num, by norm_num, rfl⟩
      ⟨0, 4, by norm_num, by norm_num, by norm_num, rfl⟩
      ⟨by omega, by omega, ?_, by omega⟩ ⟨by omega, by omega, ?_, ?_⟩ ?_ ?_
    · intro e; exact absurd (hfree 0 2 4 (by omega) (by omega) (by omega) (by omega)) (by decide)
    · intro e; exact absurd (hfree 0 1 3 (by omega) (by omega) (by omega) (by omega)) (by decide)
    · intro e; exact absurd (hfree 0 1 2 (by omega) (by omega) (by omega) (by omega)) (by decide)
    · intro p q hp hpq hq
      have hp4 : p < 4 := by omega
      interval_cases p <;> interval_cases q <;> omega
    · intro p q hp hpq hq
      have hp4 : p < 4 := by omega
      interval_cases p <;> interval_cases q
      · intro e; exact absurd (hfree 1 3 4 (by omega) (by omega) (by omega) (by omega)) (by decide)
      all_goals omega
  · obtain ⟨u, hu, huQ, huR⟩ := u_gen 5 a hmono hfree le_rfl
    refine build u (a 1 + a 4) (by omega) ?_ ⟨1, 4, by norm_num, by norm_num, by norm_num, rfl⟩
      huQ ⟨by omega, by omega, by omega, by omega⟩ huR ?_
    · rcases hu with rfl | rfl
      · exact ⟨0, 3, by norm_num, by norm_num, by norm_num, rfl⟩
      · exact ⟨0, 4, by norm_num, by norm_num, by norm_num, rfl⟩
    · intro p q hp hpq hq
      have hp4 : p < 4 := by omega
      interval_cases p <;> interval_cases q <;> omega

-- The hard case of the six-point base: if `[36] = [45]`, `[16]` is not a new value and each of
-- the pairs `[14],[15]` and `[25],[26]` has a collision, there is a three-term progression.
theorem hard6 (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) (h34 : a 3 < a 4)
    (h45 : a 4 < a 5)
    (hfree : ∀ i j k, i < 6 → j < 6 → k < 6 → a i + a k = a j + a j → i = j)
    (E : a 2 + a 5 = a 3 + a 4)
    (Hu : a 0 + a 3 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 3 ∨ a 0 + a 4 = a 2 + a 3)
    (Hv : a 1 + a 4 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 4 ∨ a 1 + a 5 = a 3 + a 4)
    (H16 : a 0 + a 5 = a 1 + a 2 ∨ a 0 + a 5 = a 1 + a 3 ∨ a 0 + a 5 = a 2 + a 3 ∨ a 0 + a 5 = a 2 + a 4 ∨ a 0 + a 5 = a 3 + a 4 ∨ a 0 + a 5 = a 1 + a 4) : False := by
  rcases Hu with e1 | e1 | e1 | e1
  · rcases Hv with e2 | e2 | e2 | e2
    · exact absurd (hfree 0 2 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 2 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · omega
  · rcases Hv with e2 | e2 | e2 | e2
    · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 2 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · omega
  · rcases Hv with e2 | e2 | e2 | e2
    · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 1 2 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 2 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · omega
  · exact absurd (hfree 0 3 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)

-- Twelve sums of six elements. The sums involving `a 0` or `a 1` outside the sums of
-- `a 2, …, a 5` number at least six (`[12], [13], [23], [24]`, `u`, `v`), the latter number at
-- least five and exactly six unless `[36] = [45]`; in that case a seventh sum among the former
-- comes from `[16]`, from both `[14], [15]` or from both `[25], [26]`, by `hard6`.
theorem six_base (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < 6 → a i < a j)
    (hfree : ∀ i j k, i < 6 → j < 6 → k < 6 → a i + a k = a j + a j → i = j) :
    12 ≤ (Dt 6 a).card := by
  have h01 := hmono 0 1 (by norm_num) (by norm_num)
  have h12 := hmono 1 2 (by norm_num) (by norm_num)
  have h23 := hmono 2 3 (by norm_num) (by norm_num)
  have h34 := hmono 3 4 (by norm_num) (by norm_num)
  have h45 := hmono 4 5 (by norm_num) (by norm_num)
  obtain ⟨u, hu, huQ, huR⟩ := u_gen 6 a hmono hfree (by norm_num)
  obtain ⟨v, hv, hvQ, hvR⟩ := v_gen 6 a hmono hfree le_rfl
  obtain ⟨u1, u2, u3, u4⟩ := huQ
  obtain ⟨v1, v2, v3, v4⟩ := hvQ
  have huv : u < v := by omega
  -- the sums of `a 2, …, a 5`
  have hR : ∀ z ∈ ({a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 4, a 3 + a 5, a 4 + a 5} : Finset ℕ),
      ∃ p q, 2 ≤ p ∧ p < q ∧ q < 6 ∧ z = a p + a q := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 3, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨2, 4, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨2, 5, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 4, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 5, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨4, 5, by norm_num, by norm_num, by norm_num, rfl⟩
  -- the six "left" sums and the "right" sums, and their disjoint union inside `Dt 6 a`
  have main : ∀ (L : Finset ℕ), (∀ x ∈ L, ∃ i j, i < 2 ∧ i < j ∧ j < 6 ∧ x = a i + a j) →
      (∀ x ∈ L, ∀ p q, 2 ≤ p → p < q → q < 6 → x ≠ a p + a q) →
      L.card + ({a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 4, a 3 + a 5, a 4 + a 5} : Finset ℕ).card
        ≤ (Dt 6 a).card := by
    intro L hL hLR
    have hdisj : Disjoint L ({a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 4, a 3 + a 5, a 4 + a 5} :
        Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨p, q, hp, hpq, hq, rfl⟩ := hR x hx'
      exact hLR _ hx p q hp hpq hq rfl
    rw [← Finset.card_union_of_disjoint hdisj]
    apply Finset.card_le_card
    intro x hx
    rw [mem_Dt]
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨i, j, _, hij, hj, rfl⟩ := hL x h; exact ⟨i, j, hij, hj, rfl⟩
    · obtain ⟨p, q, _, hpq, hq, rfl⟩ := hR x h; exact ⟨p, q, hpq, hq, rfl⟩
  -- the six left sums
  have hL6 : ∀ x ∈ insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ)),
      ∃ i j, i < 2 ∧ i < j ∧ j < 6 ∧ x = a i + a j := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hv with rfl | rfl
      · exact ⟨1, 4, by norm_num, by norm_num, by norm_num, rfl⟩
      · exact ⟨1, 5, by norm_num, by norm_num, by norm_num, rfl⟩
    · rcases hu with rfl | rfl
      · exact ⟨0, 3, by norm_num, by norm_num, by norm_num, rfl⟩
      · exact ⟨0, 4, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨0, 1, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨0, 2, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨1, 2, by norm_num, by norm_num, by norm_num, rfl⟩
    · exact ⟨1, 3, by norm_num, by norm_num, by norm_num, rfl⟩
  have hL6R : ∀ x ∈ insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ)),
      ∀ p q, 2 ≤ p → p < q → q < 6 → x ≠ a p + a q := by
    intro x hx p q hp hpq hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | hx
    · exact hvR p q hp hpq hq
    · exact huR p q hp hpq hq
    · have hp5 : p < 5 := by omega
      rcases hx with rfl | rfl | rfl | rfl <;> interval_cases p <;> interval_cases q <;> omega
  have hu' : u ∉ ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨u1, u2, u3, u4⟩
  have hv' : v ∉ insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv.ne', v1, v2, v3, v4⟩
  have hcard6 : (insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ))).card
      = 6 := by
    rw [Finset.card_insert_of_notMem hv', Finset.card_insert_of_notMem hu',
      SqueezeBench.Roth.Upper.V006.Q_card a h01 h12 h23]
  by_cases E : a 2 + a 5 = a 3 + a 4
  swap
  · -- six right sums
    have hcardR : ({a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 4, a 3 + a 5, a 4 + a 5} : Finset ℕ).card
        = 6 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] <;> omega
    have := main _ hL6 hL6R
    omega
  · -- five right sums, and a seventh left sum `w`
    have hcardR : 5 ≤ ({a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 4, a 3 + a 5, a 4 + a 5} :
        Finset ℕ).card := by
      have : ({a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 4, a 3 + a 5, a 4 + a 5} : Finset ℕ)
          = {a 2 + a 3, a 2 + a 4, a 2 + a 5, a 3 + a 5, a 4 + a 5} := by
        rw [E]
        ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [this, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] <;> omega
    -- a seventh left sum `w`, new and different from `u`, `v`
    suffices hw : ∃ w, (∃ i j, i < 2 ∧ i < j ∧ j < 6 ∧ w = a i + a j) ∧ NewQ a w ∧
        (∀ p q, 2 ≤ p → p < q → q < 6 → w ≠ a p + a q) ∧ w ≠ u ∧ w ≠ v by
      obtain ⟨w, hw, ⟨w1, w2, w3, w4⟩, hwR, hwu, hwv⟩ := hw
      have hw' : w ∉ insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} :
          Finset ℕ)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hwv, hwu, w1, w2, w3, w4⟩
      have hL7 : ∀ x ∈ insert w (insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} :
          Finset ℕ))), ∃ i j, i < 2 ∧ i < j ∧ j < 6 ∧ x = a i + a j := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hw
        · exact hL6 x hx
      have hL7R : ∀ x ∈ insert w (insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} :
          Finset ℕ))), ∀ p q, 2 ≤ p → p < q → q < 6 → x ≠ a p + a q := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hwR
        · exact hL6R x hx
      have := main _ hL7 hL7R
      rw [Finset.card_insert_of_notMem hw', hcard6] at this
      omega
    have hu16 : u ≠ a 0 + a 5 := by omega
    -- `[16]` new and different from `[25]`?
    by_cases H16 : a 0 + a 5 = a 1 + a 2 ∨ a 0 + a 5 = a 1 + a 3 ∨ a 0 + a 5 = a 2 + a 3 ∨
        a 0 + a 5 = a 2 + a 4 ∨ a 0 + a 5 = a 3 + a 4 ∨ a 0 + a 5 = a 1 + a 4
    swap
    · push Not at H16
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := H16
      refine ⟨a 0 + a 5, ⟨0, 5, by norm_num, by norm_num, by norm_num, rfl⟩,
        ⟨by omega, by omega, n1, n2⟩, ?_, hu16.symm, ?_⟩
      · intro p q hp hpq hq
        have hp5 : p < 5 := by omega
        interval_cases p <;> interval_cases q
        · exact n3
        · exact n4
        · omega
        · exact n5
        · omega
        · omega
      · rcases hv with rfl | rfl
        · exact n6
        · omega
    -- both `[14]` and `[15]` new?
    by_cases Hu : a 0 + a 3 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 3 ∨
        a 0 + a 4 = a 2 + a 3
    swap
    · clear H16
      push Not at Hu
      obtain ⟨n1, n2, n3, n4⟩ := Hu
      -- `w` is whichever of `[14]`, `[15]` is not `u`
      rcases hu with rfl | rfl
      · refine ⟨a 0 + a 4, ⟨0, 4, by norm_num, by norm_num, by norm_num, rfl⟩,
          ⟨by omega, by omega, n2, n3⟩, ?_, by omega, by omega⟩
        intro p q hp hpq hq
        have hp5 : p < 5 := by omega
        interval_cases p <;> interval_cases q
        · exact n4
        all_goals omega
      · refine ⟨a 0 + a 3, ⟨0, 3, by norm_num, by norm_num, by norm_num, rfl⟩,
          ⟨by omega, by omega, n1, by omega⟩, ?_, by omega, by omega⟩
        intro p q hp hpq hq
        have hp5 : p < 5 := by omega
        interval_cases p <;> interval_cases q <;> omega
    -- both `[25]` and `[26]` new?
    by_cases Hv : a 1 + a 4 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 4 ∨
        a 1 + a 5 = a 3 + a 4
    swap
    · clear H16 Hu
      push Not at Hv
      obtain ⟨n1, n2, n3, n4⟩ := Hv
      -- `w` is whichever of `[25]`, `[26]` is not `v`
      rcases hv with rfl | rfl
      · refine ⟨a 1 + a 5, ⟨1, 5, by norm_num, by norm_num, by norm_num, rfl⟩,
          ⟨by omega, by omega, by omega, by omega⟩, ?_, by omega, by omega⟩
        intro p q hp hpq hq
        have hp5 : p < 5 := by omega
        interval_cases p <;> interval_cases q
        · exact n2
        · exact n3
        · omega
        · exact n4
        all_goals omega
      · refine ⟨a 1 + a 4, ⟨1, 4, by norm_num, by norm_num, by norm_num, rfl⟩,
          ⟨by omega, by omega, by omega, by omega⟩, ?_, by omega, by omega⟩
        intro p q hp hpq hq
        have hp5 : p < 5 := by omega
        interval_cases p <;> interval_cases q
        · exact n1
        all_goals omega
    exact (hard6 a h01 h12 h23 h34 h45 hfree E Hu Hv H16).elim

/-! ### The count with its true base cases: `7t ≤ 2 |A +̂ A| + 18` -/

theorem count_index (t : ℕ) : ∀ (a : ℕ → ℕ), (∀ i j, i < j → j < t → a i < a j) →
    (∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) →
    7 * t ≤ 2 * (Dt t a).card + 18 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro a hmono hfree
  by_cases ht : t < 5
  · have := SqueezeBench.Roth.Upper.V005.moser_index t a hmono hfree (Dt t a)
      (fun i j hij hj => mem_Dt.mpr ⟨i, j, hij, hj, rfl⟩)
    omega
  by_cases ht5 : t = 5
  · subst ht5; have := five_base a hmono hfree; omega
  by_cases ht6 : t = 6
  · subst ht6; have := six_base a hmono hfree; omega
  obtain ⟨N, hN, hND, hR⟩ := SqueezeBench.Roth.Upper.V006.del_two t a hmono hfree (by omega)
  have ih' := ih (t - 2) (by omega) (fun i => a (i + 2))
    (fun i j hij hj => hmono (i + 2) (j + 2) (by omega) (by omega))
    (fun i j k hi hj hk h => by
      have := hfree (i + 2) (j + 2) (k + 2) (by omega) (by omega) (by omega) h
      omega)
  have hsub : Dt (t - 2) (fun i => a (i + 2)) ∪ N ⊆ Dt t a := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨i, j, hij, hj, rfl⟩ := mem_Dt.mp h
      exact mem_Dt.mpr ⟨i + 2, j + 2, by omega, by omega, rfl⟩
    · exact hND h
  have hdisj : Disjoint (Dt (t - 2) (fun i => a (i + 2))) N := by
    rw [Finset.disjoint_left]
    intro x hx hxN
    obtain ⟨i, j, hij, hj, rfl⟩ := mem_Dt.mp hx
    exact hR _ hxN (i + 2) (j + 2) (by omega) (by omega) (by omega) rfl
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hN] at this
  omega

theorem count_sums (A : Finset ℕ) (hA : ThreeAPFree (A : Set ℕ)) :
    7 * A.card ≤ 2 * (SqueezeBench.Roth.Upper.V005.sums A).card + 18 := by
  set t := A.card with ht
  let e := A.orderEmbOfFin ht.symm
  let a : ℕ → ℕ := fun i => if h : i < t then e ⟨i, h⟩ else 0
  have ha : ∀ i (h : i < t), a i = e ⟨i, h⟩ := fun i h => by simp [a, h]
  have hmono : ∀ i j, i < j → j < t → a i < a j := by
    intro i j hij hj
    rw [ha i (by omega), ha j hj]
    exact e.strictMono (Fin.mk_lt_mk.mpr hij)
  have hmem : ∀ i, i < t → a i ∈ A := fun i h => by rw [ha i h]; exact A.orderEmbOfFin_mem _ _
  have hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j := by
    intro i j k hi hj hk h
    have h1 := hA (Finset.mem_coe.mpr (hmem i hi)) (Finset.mem_coe.mpr (hmem j hj))
      (Finset.mem_coe.mpr (hmem k hk)) h
    rw [ha i hi, ha j hj] at h1
    exact Fin.mk.inj_iff.mp (e.injective h1)
  have hsub : Dt t a ⊆ SqueezeBench.Roth.Upper.V005.sums A := by
    intro x hx
    obtain ⟨i, j, hij, hj, rfl⟩ := mem_Dt.mp hx
    exact SqueezeBench.Roth.Upper.V005.mem_sums (hmem i (by omega)) (hmem j hj) (hmono i j hij hj)
  have := Finset.card_le_card hsub
  have := count_index t a hmono hfree
  omega

theorem arith {n k e₀ e₁ : ℕ} (h₀ : 2 * k + 7 * e₀ ≤ 2 * n + 18) (h₁ : 2 * k + 7 * e₁ ≤ 2 * n + 18)
    (hs : e₀ + e₁ = k) : k ≤ v n := by
  unfold v
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
  · apply le_max_of_le_left
    rcases le_total e₁ e₀ with h | h <;> omega
  · apply le_max_of_le_right
    rcases le_total e₁ e₀ with h | h <;> omega

theorem v_roth (n : ℕ) : rothNumberNat n ≤ v n := by
  obtain ⟨S, hts, hcard, hfree⟩ := rothNumberNat_spec n
  have hlt : ∀ x ∈ S, x < n := fun x hx => Finset.mem_range.mp (hts hx)
  have hsub₀ : S.filter (fun x => x % 2 = 0) ⊆ S := Finset.filter_subset _ _
  have hsub₁ : S.filter (fun x => ¬ x % 2 = 0) ⊆ S := Finset.filter_subset _ _
  have h₀ := SqueezeBench.Roth.Upper.V005.key n S hlt hfree _ hsub₀ 0
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have h₁ := SqueezeBench.Roth.Upper.V005.key n S hlt hfree _ hsub₁ 1
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)
  have m₀ := count_sums _ (hfree.mono (Finset.coe_subset.mpr hsub₀))
  have m₁ := count_sums _ (hfree.mono (Finset.coe_subset.mpr hsub₁))
  have hsplit : (S.filter (fun x => x % 2 = 0)).card
      + (S.filter (fun x => ¬ (x % 2 = 0))).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun x => x % 2 = 0)
  rw [← hcard]
  exact arith (by omega) (by omega) hsplit

/-! ### The obligations -/

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f v :=
  fun n => le_trans (SqueezeBench.Roth.Upper.V003.f_le_roth n) (v_roth n)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V006.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V006.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V006.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 100) (by decide) (by decide)

end SqueezeBench.Roth.Upper.V007
