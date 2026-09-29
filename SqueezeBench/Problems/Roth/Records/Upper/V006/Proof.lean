import SqueezeBench.Problems.Roth.Records.Upper.V006.Def
import SqueezeBench.Problems.Roth.Records.Upper.V005.Proof

/-! Record V006 for Roth, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V006.lean`. -/

namespace SqueezeBench.Roth.Upper.V006

/-! ### The seven-point lemma

For a 3-AP-free `a 0 < a 1 < … < a 6`, at least seven of the sums involving `a 0` or `a 1` are
distinct and are not sums of two of `a 2, …, a 6`. Write `[ij]` for `a (i-1) + a (j-1)`. The four
sums `[12] < [13] < [23] < [24]` lie below `[34]`, the least sum of the rest. By Moser's argument
one of `[14], [15]` and one of `[25], [26]` is new (`u_spec`, `v_spec`), and they are distinct.
A third one comes from `[27]`, `[17]` or `[16]` unless each of them coincides with an earlier
sum; if moreover neither pair `[14], [15]` nor `[25], [26]` is entirely new, a case analysis over
the possible coincidences (`hard`, 128 leaves, each closed by `omega` or by one explicit
three-term progression) shows that the configuration cannot be 3-AP-free. The reconstruction of
Moser's argument in this form came from a consultation; the case tree was found mechanically
and is checked here step by step. (L. Moser, *On non-averaging sets of integers*, Canad. J.
Math. 5 (1953), 245–252.) -/

-- The hard case of the seven-point lemma: if neither `[27]`, `[17]`, `[16]` is a new value,
-- and each of the pairs `[14],[15]` and `[25],[26]` has a collision, there is a 3-AP.
theorem hard (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) (h34 : a 3 < a 4)
    (h45 : a 4 < a 5) (h56 : a 5 < a 6)
    (hfree : ∀ i j k, i < 7 → j < 7 → k < 7 → a i + a k = a j + a j → i = j)
    (Hu : a 0 + a 3 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 3 ∨ a 0 + a 4 = a 2 + a 3)
    (Hv : a 1 + a 4 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 4 ∨ a 1 + a 5 = a 3 + a 4)
    (H16 : a 0 + a 5 = a 1 + a 2 ∨ a 0 + a 5 = a 1 + a 3 ∨ a 0 + a 5 = a 2 + a 3 ∨ a 0 + a 5 = a 2 + a 4 ∨ a 0 + a 5 = a 3 + a 4 ∨ a 0 + a 5 = a 1 + a 4)
    (H17 : a 0 + a 6 = a 1 + a 2 ∨ a 0 + a 6 = a 1 + a 3 ∨ a 0 + a 6 = a 1 + a 4 ∨ a 0 + a 6 = a 1 + a 5 ∨ a 0 + a 6 = a 2 + a 3 ∨ a 0 + a 6 = a 2 + a 4 ∨ a 0 + a 6 = a 2 + a 5 ∨ a 0 + a 6 = a 3 + a 4 ∨ a 0 + a 6 = a 3 + a 5 ∨ a 0 + a 6 = a 4 + a 5)
    (H27 : a 1 + a 6 = a 2 + a 3 ∨ a 1 + a 6 = a 2 + a 4 ∨ a 1 + a 6 = a 2 + a 5 ∨ a 1 + a 6 = a 3 + a 4 ∨ a 1 + a 6 = a 3 + a 5 ∨ a 1 + a 6 = a 4 + a 5) : False := by
  rcases Hu with e1 | e1 | e1 | e1
  · rcases Hv with e2 | e2 | e2 | e2
    · exact absurd (hfree 0 2 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 2 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · exact absurd (hfree 2 3 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
      · exact absurd (hfree 1 3 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
      · omega
      · omega
      · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · omega
      · omega
      · rcases H17 with e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4
        · omega
        · omega
        · omega
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
          · omega
          · omega
        · omega
        · omega
        · exact absurd (hfree 4 5 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
          · omega
          · omega
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · omega
          · omega
          · omega
          · exact absurd (hfree 0 3 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · exact absurd (hfree 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
      · omega
      · omega
  · rcases Hv with e2 | e2 | e2 | e2
    · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
      · omega
      · omega
      · omega
      · exact absurd (hfree 2 4 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 2 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · omega
      · rcases H17 with e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4
        · omega
        · omega
        · exact absurd (hfree 2 4 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
          · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
        · omega
        · exact absurd (hfree 1 4 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · exact absurd (hfree 3 5 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
          · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
        · exact absurd (hfree 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
      · omega
      · omega
      · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
  · rcases Hv with e2 | e2 | e2 | e2
    · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact absurd (hfree 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · omega
      · rcases H17 with e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4 | e4
        · omega
        · omega
        · exact absurd (hfree 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · exact absurd (hfree 0 3 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
        · omega
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · exact absurd (hfree 0 3 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
          · omega
        · exact absurd (hfree 3 5 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · exact absurd (hfree 1 4 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · exact absurd (hfree 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
        · rcases H27 with e5 | e5 | e5 | e5 | e5 | e5
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
      · omega
      · omega
      · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · exact absurd (hfree 0 3 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
  · rcases Hv with e2 | e2 | e2 | e2
    · omega
    · omega
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact absurd (hfree 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · rcases H16 with e3 | e3 | e3 | e3 | e3 | e3
      · omega
      · omega
      · omega
      · exact absurd (hfree 1 3 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
      · omega
      · exact absurd (hfree 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
-- `x` is none of the four smallest sums `[12], [13], [23], [24]`.
def NewQ (a : ℕ → ℕ) (x : ℕ) : Prop :=
  x ≠ a 0 + a 1 ∧ x ≠ a 0 + a 2 ∧ x ≠ a 1 + a 2 ∧ x ≠ a 1 + a 3

-- `x` is no sum of two of `a 2, …, a 6`.
def NewR (a : ℕ → ℕ) (x : ℕ) : Prop :=
  ∀ p q, 2 ≤ p → p < q → q < 7 → x ≠ a p + a q

theorem Q_card (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) :
    ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton] <;> simp only [Finset.mem_insert, Finset.mem_singleton, not_or] <;> omega

theorem Q_R (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) (h34 : a 3 < a 4)
    (h45 : a 4 < a 5) (h56 : a 5 < a 6) :
    ∀ x ∈ ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ), NewR a x := by
  intro x hx p q hp hpq hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  have hp7 : p < 7 := by omega
  rcases hx with rfl | rfl | rfl | rfl <;> interval_cases p <;> interval_cases q <;> omega

-- One of `[14]`, `[15]` is new (Moser).

theorem u_spec (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) (h34 : a 3 < a 4)
    (h45 : a 4 < a 5) (h56 : a 5 < a 6)
    (hfree : ∀ i j k, i < 7 → j < 7 → k < 7 → a i + a k = a j + a j → i = j) :
    ∃ u, (u = a 0 + a 3 ∨ u = a 0 + a 4) ∧ NewQ a u ∧ NewR a u := by
  by_cases h : a 0 + a 3 = a 1 + a 2
  · refine ⟨a 0 + a 4, Or.inr rfl, ⟨by omega, by omega, by omega, ?_⟩, ?_⟩
    · intro e
      exact absurd (hfree 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · intro p q hp hpq hq
      have hp7 : p < 7 := by omega
      interval_cases p <;> interval_cases q
      · intro e
        exact absurd (hfree 1 3 4 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
      all_goals omega
  · refine ⟨a 0 + a 3, Or.inl rfl, ⟨by omega, by omega, h, by omega⟩, ?_⟩
    intro p q hp hpq hq
    have hp7 : p < 7 := by omega
    interval_cases p <;> interval_cases q <;> omega

-- One of `[25]`, `[26]` is new (Moser).

theorem v_spec (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) (h34 : a 3 < a 4)
    (h45 : a 4 < a 5) (h56 : a 5 < a 6)
    (hfree : ∀ i j k, i < 7 → j < 7 → k < 7 → a i + a k = a j + a j → i = j) :
    ∃ v, (v = a 1 + a 4 ∨ v = a 1 + a 5) ∧ NewQ a v ∧ NewR a v := by
  by_cases h : a 1 + a 4 = a 2 + a 3
  · refine ⟨a 1 + a 5, Or.inr rfl, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro p q hp hpq hq
    have hp7 : p < 7 := by omega
    interval_cases p <;> interval_cases q
    · omega
    · intro e
      exact absurd (hfree 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    · omega
    · omega
    · intro e
      exact absurd (hfree 2 4 5 (by norm_num) (by norm_num) (by norm_num) (by omega)) (by decide)
    all_goals omega
  · refine ⟨a 1 + a 4, Or.inl rfl, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro p q hp hpq hq
    have hp7 : p < 7 := by omega
    interval_cases p <;> interval_cases q <;> omega

-- Seven pairwise distinct sums involving `a 0` or `a 1`, none a sum of two of `a 2, …, a 6`.

theorem assemble (a : ℕ → ℕ) (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) (h34 : a 3 < a 4)
    (h45 : a 4 < a 5) (h56 : a 5 < a 6) (u v w : ℕ)
    (hu : u = a 0 + a 3 ∨ u = a 0 + a 4) (hv : v = a 1 + a 4 ∨ v = a 1 + a 5)
    (hw : ∃ i j, i < 2 ∧ i < j ∧ j < 7 ∧ w = a i + a j)
    (huQ : NewQ a u) (hvQ : NewQ a v) (hwQ : NewQ a w)
    (huR : NewR a u) (hvR : NewR a v) (hwR : NewR a w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ N : Finset ℕ, N.card = 7 ∧ (∀ x ∈ N, ∃ i j, i < 2 ∧ i < j ∧ j < 7 ∧ x = a i + a j) ∧
      (∀ x ∈ N, ∀ p q, 2 ≤ p → p < q → q < 7 → x ≠ a p + a q) := by
  obtain ⟨u1, u2, u3, u4⟩ := huQ
  obtain ⟨v1, v2, v3, v4⟩ := hvQ
  obtain ⟨w1, w2, w3, w4⟩ := hwQ
  have hu' : u ∉ ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨u1, u2, u3, u4⟩
  have hv' : v ∉ insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => huv e.symm, v1, v2, v3, v4⟩
  have hw' : w ∉ insert v (insert u ({a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3} : Finset ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => hvw e.symm, fun e => huw e.symm, w1, w2, w3, w4⟩
  refine ⟨insert w (insert v (insert u {a 0 + a 1, a 0 + a 2, a 1 + a 2, a 1 + a 3})), ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hw', Finset.card_insert_of_notMem hv',
      Finset.card_insert_of_notMem hu', Q_card a h01 h12 h23]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw
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
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact hwR
    · exact hvR
    · exact huR
    · exact Q_R a h01 h12 h23 h34 h45 h56 _ (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact hx)

-- The seven-point lemma.

theorem seven_new (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < 7 → a i < a j)
    (hfree : ∀ i j k, i < 7 → j < 7 → k < 7 → a i + a k = a j + a j → i = j) :
    ∃ N : Finset ℕ, N.card = 7 ∧ (∀ x ∈ N, ∃ i j, i < 2 ∧ i < j ∧ j < 7 ∧ x = a i + a j) ∧
      (∀ x ∈ N, ∀ p q, 2 ≤ p → p < q → q < 7 → x ≠ a p + a q) := by
  have h01 := hmono 0 1 (by norm_num) (by norm_num)
  have h12 := hmono 1 2 (by norm_num) (by norm_num)
  have h23 := hmono 2 3 (by norm_num) (by norm_num)
  have h34 := hmono 3 4 (by norm_num) (by norm_num)
  have h45 := hmono 4 5 (by norm_num) (by norm_num)
  have h56 := hmono 5 6 (by norm_num) (by norm_num)
  clear hmono
  obtain ⟨u, hu, huQ, huR⟩ := u_spec a h01 h12 h23 h34 h45 h56 hfree
  obtain ⟨v, hv, hvQ, hvR⟩ := v_spec a h01 h12 h23 h34 h45 h56 hfree
  -- order facts that hold in every case
  have huv : u ≠ v := by omega
  have hu27 : u ≠ a 1 + a 6 := by omega
  have hv27 : v ≠ a 1 + a 6 := by omega
  have hu17 : u ≠ a 0 + a 6 := by omega
  have hu16 : u ≠ a 0 + a 5 := by omega
  have Q27 : NewQ a (a 1 + a 6) := ⟨by omega, by omega, by omega, by omega⟩
  have Q17a : a 0 + a 6 ≠ a 0 + a 1 := by omega
  have Q17b : a 0 + a 6 ≠ a 0 + a 2 := by omega
  have Q16a : a 0 + a 5 ≠ a 0 + a 1 := by omega
  have Q16b : a 0 + a 5 ≠ a 0 + a 2 := by omega
  have Q25 : NewQ a (a 1 + a 4) := ⟨by omega, by omega, by omega, by omega⟩
  have Q26 : NewQ a (a 1 + a 5) := ⟨by omega, by omega, by omega, by omega⟩
  have Q14a : a 0 + a 3 ≠ a 0 + a 1 := by omega
  have Q14b : a 0 + a 3 ≠ a 0 + a 2 := by omega
  have Q14d : a 0 + a 3 ≠ a 1 + a 3 := by omega
  have Q15a : a 0 + a 4 ≠ a 0 + a 1 := by omega
  have Q15b : a 0 + a 4 ≠ a 0 + a 2 := by omega
  have d1 : a 0 + a 3 ≠ a 0 + a 4 := by omega
  have d2 : a 1 + a 4 ≠ a 1 + a 5 := by omega
  have d3 : a 0 + a 3 ≠ v := by omega
  have d4 : a 0 + a 4 ≠ v := by omega
  have d5 : u ≠ a 1 + a 4 := by omega
  have d6 : u ≠ a 1 + a 5 := by omega
  -- `[27]` new?
  by_cases H27 : a 1 + a 6 = a 2 + a 3 ∨ a 1 + a 6 = a 2 + a 4 ∨ a 1 + a 6 = a 2 + a 5 ∨
      a 1 + a 6 = a 3 + a 4 ∨ a 1 + a 6 = a 3 + a 5 ∨ a 1 + a 6 = a 4 + a 5
  swap
  · push Not at H27
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := H27
    refine assemble a h01 h12 h23 h34 h45 h56 u v (a 1 + a 6) hu hv
      ⟨1, 6, by norm_num, by norm_num, by norm_num, rfl⟩ huQ hvQ Q27 huR hvR ?_ huv hu27 hv27
    intro p q hp hpq hq
    have hp7 : p < 7 := by omega
    interval_cases p <;> interval_cases q
    · exact n1
    · exact n2
    · exact n3
    · omega
    · exact n4
    · exact n5
    · omega
    · exact n6
    · omega
    · omega
  -- `[17]` new?
  by_cases H17 : a 0 + a 6 = a 1 + a 2 ∨ a 0 + a 6 = a 1 + a 3 ∨ a 0 + a 6 = a 1 + a 4 ∨
      a 0 + a 6 = a 1 + a 5 ∨ a 0 + a 6 = a 2 + a 3 ∨ a 0 + a 6 = a 2 + a 4 ∨ a 0 + a 6 = a 2 + a 5 ∨
      a 0 + a 6 = a 3 + a 4 ∨ a 0 + a 6 = a 3 + a 5 ∨ a 0 + a 6 = a 4 + a 5
  swap
  · clear H27
    push Not at H17
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := H17
    have hv17 : v ≠ a 0 + a 6 := by
      rcases hv with rfl | rfl
      · exact fun e => n3 e.symm
      · exact fun e => n4 e.symm
    refine assemble a h01 h12 h23 h34 h45 h56 u v (a 0 + a 6) hu hv
      ⟨0, 6, by norm_num, by norm_num, by norm_num, rfl⟩ huQ hvQ ⟨Q17a, Q17b, n1, n2⟩ huR hvR ?_
      huv hu17 hv17
    intro p q hp hpq hq
    have hp7 : p < 7 := by omega
    interval_cases p <;> interval_cases q
    · exact n5
    · exact n6
    · exact n7
    · omega
    · exact n8
    · exact n9
    · omega
    · exact n10
    · omega
    · omega
  -- `[16]` new and different from `[25]`?
  by_cases H16 : a 0 + a 5 = a 1 + a 2 ∨ a 0 + a 5 = a 1 + a 3 ∨ a 0 + a 5 = a 2 + a 3 ∨
      a 0 + a 5 = a 2 + a 4 ∨ a 0 + a 5 = a 3 + a 4 ∨ a 0 + a 5 = a 1 + a 4
  swap
  · clear H27 H17
    push Not at H16
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := H16
    have hv16 : v ≠ a 0 + a 5 := by
      rcases hv with rfl | rfl
      · exact fun e => n6 e.symm
      · omega
    refine assemble a h01 h12 h23 h34 h45 h56 u v (a 0 + a 5) hu hv
      ⟨0, 5, by norm_num, by norm_num, by norm_num, rfl⟩ huQ hvQ ⟨Q16a, Q16b, n1, n2⟩ huR hvR ?_
      huv hu16 hv16
    intro p q hp hpq hq
    have hp7 : p < 7 := by omega
    interval_cases p <;> interval_cases q
    · exact n3
    · exact n4
    · omega
    · omega
    · exact n5
    · omega
    · omega
    · omega
    · omega
    · omega
  -- both `[14]` and `[15]` new?
  by_cases Hu : a 0 + a 3 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 2 ∨ a 0 + a 4 = a 1 + a 3 ∨
      a 0 + a 4 = a 2 + a 3
  swap
  · clear H27 H17 H16
    push Not at Hu
    obtain ⟨n1, n2, n3, n4⟩ := Hu
    refine assemble a h01 h12 h23 h34 h45 h56 (a 0 + a 3) v (a 0 + a 4) (Or.inl rfl) hv
      ⟨0, 4, by norm_num, by norm_num, by norm_num, rfl⟩ ⟨Q14a, Q14b, n1, Q14d⟩ hvQ
      ⟨Q15a, Q15b, n2, n3⟩ ?_ hvR ?_ d3 d1 (fun e => d4 e.symm)
    · intro p q hp hpq hq
      have hp7 : p < 7 := by omega
      interval_cases p <;> interval_cases q <;> omega
    · intro p q hp hpq hq
      have hp7 : p < 7 := by omega
      interval_cases p <;> interval_cases q
      · exact n4
      all_goals omega
  -- both `[25]` and `[26]` new?
  by_cases Hv : a 1 + a 4 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 3 ∨ a 1 + a 5 = a 2 + a 4 ∨
      a 1 + a 5 = a 3 + a 4
  swap
  · clear H27 H17 H16 Hu
    push Not at Hv
    obtain ⟨n1, n2, n3, n4⟩ := Hv
    refine assemble a h01 h12 h23 h34 h45 h56 u (a 1 + a 4) (a 1 + a 5) hu (Or.inl rfl)
      ⟨1, 5, by norm_num, by norm_num, by norm_num, rfl⟩ huQ Q25 Q26 huR ?_ ?_ d5 d6 d2
    · intro p q hp hpq hq
      have hp7 : p < 7 := by omega
      interval_cases p <;> interval_cases q
      · exact n1
      all_goals omega
    · intro p q hp hpq hq
      have hp7 : p < 7 := by omega
      interval_cases p <;> interval_cases q
      · exact n2
      · exact n3
      · omega
      · omega
      · exact n4
      all_goals omega
  exact (hard a h01 h12 h23 h34 h45 h56 hfree Hu Hv H16 H17 H27).elim

-- Pairwise sums of `a 0, …, a (t-1)`.
def Dt (t : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  ((Finset.range t ×ˢ Finset.range t).filter (fun p => p.1 < p.2)).image (fun p => a p.1 + a p.2)

theorem mem_Dt {t : ℕ} {a : ℕ → ℕ} {x : ℕ} :
    x ∈ Dt t a ↔ ∃ i j, i < j ∧ j < t ∧ x = a i + a j := by
  simp only [Dt, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨hi, hj⟩, hij⟩, rfl⟩; exact ⟨i, j, hij, hj, rfl⟩
  · rintro ⟨i, j, hij, hj, rfl⟩; exact ⟨i, j, ⟨⟨by omega, hj⟩, hij⟩, rfl⟩

-- Deleting the two smallest elements kills seven sums (window form, any length `t ≥ 7`).

theorem del_two (t : ℕ) (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < t → a i < a j)
    (hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) (ht : 7 ≤ t) :
    ∃ N : Finset ℕ, N.card = 7 ∧ N ⊆ Dt t a ∧
      (∀ x ∈ N, ∀ p q, 2 ≤ p → p < q → q < t → x ≠ a p + a q) := by
  obtain ⟨N, hN, hmem, hR⟩ := seven_new a (fun i j hij hj => hmono i j hij (by omega))
    (fun i j k hi hj hk h => hfree i j k (by omega) (by omega) (by omega) h)
  refine ⟨N, hN, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, j, _, hij, hj, rfl⟩ := hmem x hx
    exact mem_Dt.mpr ⟨i, j, hij, by omega, rfl⟩
  · intro x hx p q hp hpq hq
    by_cases hq7 : q < 7
    · exact hR x hx p q hp hpq hq7
    · obtain ⟨i, j, hi, hij, hj, rfl⟩ := hmem x hx
      have hle := SqueezeBench.Roth.Upper.V005.hle_of_mono hmono
      have h1 := hle i 1 (by omega) (by omega)
      have h2 := hle j 6 (by omega) (by omega)
      have h3 := hmono 1 2 (by norm_num) (by omega)
      have h4 := hmono 6 q (by omega) hq
      have h5 := hle 2 p hp (by omega)
      omega

-- `7t ≤ 2 |Dt t a| + 20` for every 3-AP-free increasing enumeration: induction removing the
-- two smallest elements, with Moser's `3t - 7` as the base for `t ≤ 6`.

theorem count_index (t : ℕ) : ∀ (a : ℕ → ℕ), (∀ i j, i < j → j < t → a i < a j) →
    (∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) →
    7 * t ≤ 2 * (Dt t a).card + 20 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro a hmono hfree
  by_cases ht : t < 7
  · have := SqueezeBench.Roth.Upper.V005.moser_index t a hmono hfree (Dt t a)
      (fun i j hij hj => mem_Dt.mpr ⟨i, j, hij, hj, rfl⟩)
    omega
  · obtain ⟨N, hN, hND, hR⟩ := del_two t a hmono hfree (by omega)
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

-- For a 3-AP-free finset, via its increasing enumeration.

theorem count_sums (A : Finset ℕ) (hA : ThreeAPFree (A : Set ℕ)) :
    7 * A.card ≤ 2 * (SqueezeBench.Roth.Upper.V005.sums A).card + 20 := by
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

theorem arith {n k e₀ e₁ : ℕ} (h₀ : 2 * k + 7 * e₀ ≤ 2 * n + 20) (h₁ : 2 * k + 7 * e₁ ≤ 2 * n + 20)
    (hs : e₀ + e₁ = k) : k ≤ v n := by
  unfold v
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
  · apply le_max_of_le_left
    rcases le_total e₁ e₀ with h | h <;> omega
  · apply le_max_of_le_right
    rcases le_total e₁ e₀ with h | h <;> omega

theorem moser2_valid (n : ℕ) : rothNumberNat n ≤ v n := by
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
  fun n => le_trans (SqueezeBench.Roth.Upper.V003.f_le_roth n) (moser2_valid n)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V005.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V005.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 1000) (by decide) (by decide)

end SqueezeBench.Roth.Upper.V006
