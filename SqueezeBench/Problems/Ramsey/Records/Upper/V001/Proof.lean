import SqueezeBench.Problems.Ramsey.Records.Upper.V001.Def
import SqueezeBench.Problems.Ramsey.Records.Upper.V000.Proof

/-! Record V001 for Ramsey, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Upper/V001.lean`. -/

namespace SqueezeBench.Ramsey.Upper.V001

open SqueezeBench SimpleGraph Finset

/-! ## The parity refinement of the Erdős–Szekeres step -/

/-- Erdős–Szekeres with the parity saving: when `M` and `N` are both even, `M + N - 1`
vertices already force. On more than `M + N - 1` vertices the plain step applies. On
exactly `M + N - 1`, if no vertex has `M` neighbours and none has `N` non-neighbours then
every degree is exactly `M - 1`, which is odd; an odd number of vertices of odd degree
contradicts the handshake lemma. -/
theorem forcesOn_step_parity {M N s t : ℕ} (hMe : M % 2 = 0) (hNe : N % 2 = 0)
    (h1 : 1 ≤ M + N) (hM : ForcesOn M s (t + 1)) (hN : ForcesOn N (s + 1) t) :
    ForcesOn (M + N - 1) (s + 1) (t + 1) := by
  intro V _ _ G hcard
  classical
  by_cases hbig : M + N ≤ Fintype.card V
  · exact forcesOn_step h1 hM hN G hbig
  have hcardeq : Fintype.card V = M + N - 1 := by omega
  by_cases hA : ∃ v : V, M ≤ (G.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hA
    have hcardA : M ≤ Fintype.card ((G.neighborFinset v : Finset V) : Set V) := by
      simp only [Finset.coe_sort_coe, Fintype.card_coe]; exact hv
    rcases hM (G.induce ((G.neighborFinset v : Finset V) : Set V)) hcardA with ⟨S, hS⟩ | ⟨T, hT⟩
    · left
      rw [isNClique_induce_iff] at hS
      refine ⟨insert v (S.map (Function.Embedding.subtype _)), hS.insert ?_⟩
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨w, _, rfl⟩ := hb
      simpa using w.2
    · right
      rw [← induce_compl, isNClique_induce_iff] at hT
      exact ⟨_, hT⟩
  by_cases hB : ∃ v : V, N ≤ (Gᶜ.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hB
    have hcardB : N ≤ Fintype.card ((Gᶜ.neighborFinset v : Finset V) : Set V) := by
      simp only [Finset.coe_sort_coe, Fintype.card_coe]; exact hv
    rcases hN (G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V)) hcardB with ⟨S, hS⟩ | ⟨T, hT⟩
    · left
      rw [isNClique_induce_iff] at hS
      exact ⟨_, hS⟩
    · right
      rw [← induce_compl, isNClique_induce_iff] at hT
      refine ⟨insert v (T.map (Function.Embedding.subtype _)), hT.insert ?_⟩
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨w, _, rfl⟩ := hb
      simpa using w.2
  exfalso
  have hA' : ∀ v : V, (G.neighborFinset v).card < M := by
    intro v; by_contra hcon; exact hA ⟨v, by omega⟩
  have hB' : ∀ v : V, (Gᶜ.neighborFinset v).card < N := by
    intro v; by_contra hcon; exact hB ⟨v, by omega⟩
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hM1 : 1 ≤ M := by have := hA' v₀; omega
  have hdeg : ∀ v : V, G.degree v = M - 1 := by
    intro v
    have h₁ := hA' v
    have h₂ := hB' v
    have hs := split_card G v
    simp only [card_neighborFinset_eq_degree] at h₁ h₂ hs
    omega
  have hsum : Fintype.card V * (M - 1) = 2 * G.edgeFinset.card := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
    simp [hdeg]
  have hc : Fintype.card V % 2 = 1 := by omega
  have hm : (M - 1) % 2 = 1 := by omega
  have hmul : (Fintype.card V * (M - 1)) % 2 = 1 := by rw [Nat.mul_mod, hc, hm]
  rw [hsum] at hmul
  omega

/-! ## The table -/

theorem stepVal_le (a b : ℕ) : stepVal a b ≤ a + b := by
  unfold stepVal; split <;> omega

theorem stepVal_pos {a b : ℕ} (h : 1 ≤ a + b) : 1 ≤ stepVal a b := by
  unfold stepVal; split
  · rename_i hab
    obtain ⟨ha, hb⟩ := hab
    omega
  · omega

theorem dRow_zero (k : ℕ) : dRow k 0 = 0 := by
  cases k <;> simp [dRow]

theorem dRow_succ (k i : ℕ) : dRow (k + 1) (i + 1) = stepVal (dRow k i) (dRow k (i + 1)) := by
  simp [dRow]

/-- Every entry strictly inside its antidiagonal is positive. -/
theorem dRow_pos : ∀ k i, 1 ≤ i → i ≤ k + 1 → 1 ≤ dRow k i := by
  intro k
  induction k with
  | zero =>
    intro i h1 h2
    have hi : i = 1 := by omega
    subst hi
    simp [dRow]
  | succ k ih =>
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [dRow_succ]
    refine stepVal_pos ?_
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have := ih (j + 1) (by omega) (by omega)
      omega
    · have := ih j (by omega) (by omega)
      omega

/-- Validity of the table, entry by entry. -/
theorem dRow_forces : ∀ k i, ForcesOn (dRow k i) i (k + 2 - i) := by
  intro k
  induction k with
  | zero =>
    intro i
    match i with
    | 0 =>
      rw [show dRow 0 0 = 0 from by simp [dRow]]
      intro V _ _
      exact forcesOn_zero_left 0 (0 + 2 - 0)
    | 1 =>
      rw [show dRow 0 1 = 1 from by simp [dRow], show 0 + 2 - 1 = 1 from rfl]
      intro V _ _
      exact forcesOn_one_left 1
    | (j + 2) =>
      rw [show 0 + 2 - (j + 2) = 0 from by omega]
      intro V _ _
      exact forcesOn_zero_right _ (j + 2)
  | succ k ih =>
    intro i
    match i with
    | 0 =>
      rw [dRow_zero]
      intro V _ _
      exact forcesOn_zero_left 0 (k + 1 + 2 - 0)
    | (j + 1) =>
      rcases Nat.lt_or_ge (k + 1) j with hj | hj
      · rw [show k + 1 + 2 - (j + 1) = 0 from by omega]
        intro V _ _
        exact forcesOn_zero_right _ (j + 1)
      · have hMv : ForcesOn (dRow k j) j (k + 1 - j + 1) := by
          have h : ForcesOn (dRow k j) j (k + 2 - j) := ih j
          rwa [show k + 2 - j = k + 1 - j + 1 from by omega] at h
        have hNv : ForcesOn (dRow k (j + 1)) (j + 1) (k + 1 - j) := by
          have h : ForcesOn (dRow k (j + 1)) (j + 1) (k + 2 - (j + 1)) := ih (j + 1)
          rwa [show k + 2 - (j + 1) = k + 1 - j from by omega] at h
        have hpos : 1 ≤ dRow k j + dRow k (j + 1) := by
          rcases Nat.eq_zero_or_pos j with hj0 | hj0
          · subst hj0
            have := dRow_pos k 1 (by omega) (by omega)
            simp only [Nat.zero_add]
            omega
          · have := dRow_pos k j hj0 (by omega)
            omega
        rw [dRow_succ, show k + 1 + 2 - (j + 1) = k + 1 - j + 1 from by omega]
        unfold stepVal
        split
        · rename_i hpar
          intro V _ _
          exact forcesOn_step_parity hpar.1 hpar.2 hpos hMv hNv
        · intro V _ _
          exact forcesOn_step hpos hMv hNv

/-! ## The obligations -/

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey.f record := by
  intro n
  rcases Nat.lt_or_ge n nMin with h | h
  · rw [SqueezeBench.Ramsey.f, if_pos h]
    exact Nat.zero_le _
  · have h2 : 2 ≤ n := by rwa [nMin_eq] at h
    have hf : ForcesOn (dRow (2 * n - 2) n) n (2 * n - 2 + 2 - n) := dRow_forces _ _
    rw [show 2 * n - 2 + 2 - n = n from by omega] at hf
    exact f_le_of_forces h (forces_of_forcesOn hf)

/-- The table never exceeds the binomial bound: Pascal's rule dominates `stepVal`. -/
theorem dRow_le_choose : ∀ k i, dRow k i ≤ Nat.choose k (i - 1) := by
  intro k
  induction k with
  | zero =>
    intro i
    match i with
    | 0 => simp [dRow]
    | 1 => simp [dRow]
    | (j + 2) => simp [dRow]
  | succ k ih =>
    intro i
    match i with
    | 0 => simp [dRow_zero]
    | (j + 1) =>
      rw [dRow_succ]
      refine le_trans (stepVal_le _ _) ?_
      match j with
      | 0 => simpa [dRow_zero] using ih 1
      | (m + 1) =>
        have h1 := ih (m + 1)
        have h2 := ih (m + 1 + 1)
        simp only [Nat.add_sub_cancel] at h1 h2 ⊢
        rw [Nat.choose_succ_succ]
        simp only [Nat.succ_eq_add_one]
        omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey.Upper.V000.record record := by
  intro n
  show dRow (2 * n - 2) n ≤ Nat.choose (2 * n - 2) (n - 1)
  exact dRow_le_choose (2 * n - 2) n

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Upper.V000.record record :=
  ⟨5, by decide, by decide +kernel⟩

end SqueezeBench.Ramsey.Upper.V001
