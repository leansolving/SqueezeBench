import SqueezeBench.Problems.Schur.Records.Upper.V001.Def
import SqueezeBench.Problems.Schur.Records.Upper.V000.Proof

/-! Record V001 for Schur, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Schur/Upper/V001.lean`. -/

namespace SqueezeBench.Schur.Upper.V001

open SqueezeBench Finset SqueezeBench.Schur

theorem ram_succ (k : ℕ) : ram (k + 1) = (k + 1) * (ram k - 1) + 2 := rfl

theorem ram_ge_two (k : ℕ) : 2 ≤ ram k := by
  induction k with
  | zero => exact Nat.le_refl 2
  | succ k _ => rw [ram_succ]; exact Nat.le_add_left 2 _

-- The recurrence `MonoTriangle N k → MonoTriangle (k+1)*(N-1)+2 (k+1)` of `Finite.lean`,
-- iterated from one colour instead of being weakened to `3 * k!`.
theorem monoTriangle_ram : ∀ k : ℕ, MonoTriangle (ram (k + 1)) (k + 1) := by
  intro k
  induction k with
  | zero =>
    have h3 : ram (0 + 1) = 3 := rfl
    rw [h3]
    intro V _ _ col hsym hcard
    exact monoTriangle_one col hsym hcard
  | succ k ih =>
    have hpos : 1 ≤ ram (k + 1) := le_trans (Nat.le_succ 1) (ram_ge_two (k + 1))
    intro V _ _ col hsym hcard
    exact monoTriangle_mono (le_of_eq (ram_succ (k + 1)).symm)
      (monoTriangle_step (Nat.le_add_left 1 k) hpos ih) col hsym hcard

-- The gap colouring of `Finite.lean`, with the Ramsey bound left as a parameter.
theorem forces_of_monoTriangle {k N : ℕ} (h : MonoTriangle (N + 1) k) : Forces k N := by
  intro c
  have hcard : N + 1 ≤ Fintype.card (Fin (N + 1)) := by simp
  have hsymc : ∀ a b : Fin (N + 1), c (gap a b) = c (gap b a) := by
    intro a b; rw [gap_comm]
  obtain ⟨ι, S, hScard, hSmono⟩ := h (fun a b : Fin (N + 1) => c (gap a b)) hsymc hcard
  set w : Fin 3 → Fin (N + 1) := fun i => (S.orderIsoOfFin hScard i : Fin (N + 1)) with hw
  have hwmem : ∀ i, w i ∈ S := fun i => (S.orderIsoOfFin hScard i).2
  have hwlt : ∀ i j : Fin 3, i < j → (w i : ℕ) < (w j : ℕ) := by
    intro i j hij
    have h : (S.orderIsoOfFin hScard i : Fin (N + 1)) < (S.orderIsoOfFin hScard j) := by
      exact_mod_cast (S.orderIsoOfFin hScard).lt_iff_lt.mpr hij
    exact h
  have hwne : ∀ i j : Fin 3, i < j → w i ≠ w j := by
    intro i j hij he
    exact absurd (congrArg (fun z : Fin (N + 1) => (z : ℕ)) he) (Nat.ne_of_lt (hwlt i j hij))
  have hcol : ∀ i j : Fin 3, i < j → c ((w j : ℕ) - (w i : ℕ)) = ι := by
    intro i j hij
    have h := hSmono _ (hwmem i) _ (hwmem j) (hwne i j hij)
    rwa [gap_of_lt (hwlt i j hij)] at h
  have hb : ∀ i : Fin 3, (w i : ℕ) ≤ N := fun i => Nat.lt_succ_iff.mp (w i).isLt
  have h01 := hwlt 0 1 (by decide)
  have h12 := hwlt 1 2 (by decide)
  have h02 := hwlt 0 2 (by decide)
  refine ⟨(w 1 : ℕ) - (w 0 : ℕ), ?_, (w 2 : ℕ) - (w 1 : ℕ), ?_,
    (w 2 : ℕ) - (w 0 : ℕ), ?_, ?_, ?_, ?_⟩
  · rw [mem_Icc]; have := hb 1; omega
  · rw [mem_Icc]; have := hb 2; omega
  · rw [mem_Icc]; have := hb 2; omega
  · omega
  · rw [hcol 0 1 (by decide), hcol 1 2 (by decide)]
  · rw [hcol 1 2 (by decide), hcol 0 2 (by decide)]

-- `ram k` points force: `S(k) ≤ ram k - 2`.
theorem forces_ram (k : ℕ) : Forces (k + 1) (ram (k + 1) - 1) := by
  have h2 : 2 ≤ ram (k + 1) := ram_ge_two (k + 1)
  obtain ⟨N, hN⟩ : ∃ N, ram (k + 1) = N + 1 := ⟨ram (k + 1) - 1, by omega⟩
  rw [hN, Nat.add_sub_cancel]
  refine forces_of_monoTriangle (N := N) (k := k + 1) ?_
  rw [← hN]
  intro V _ _ col hsym hcard
  exact monoTriangle_ram k col hsym hcard

theorem ram_le_factorial (k : ℕ) : ram k ≤ 3 * Nat.factorial k := by
  induction k with
  | zero => exact Nat.le_succ 2
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Nat.le_refl 3
    · have hpos : 1 ≤ Nat.factorial k := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
      obtain ⟨G, hG⟩ : ∃ G, 3 * Nat.factorial k = G + 1 := ⟨3 * Nat.factorial k - 1, by omega⟩
      have h2 : 2 ≤ ram k := ram_ge_two k
      calc ram (k + 1) = (k + 1) * (ram k - 1) + 2 := ram_succ k
        _ ≤ (k + 1) * G + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2
        _ ≤ (k + 1) * G + (k + 1) := Nat.add_le_add_left (by omega) _
        _ = (k + 1) * (G + 1) := by ring
        _ = (k + 1) * (3 * Nat.factorial k) := by rw [hG]
        _ = 3 * Nat.factorial (k + 1) := by rw [Nat.factorial_succ]; ring

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := by
  intro k
  rcases Nat.lt_or_ge k nMin with h | h
  · rw [f, if_pos h]
    exact Nat.zero_le _
  · have hk1 : 1 ≤ k := by simpa using h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hle := f_le_of_forces h (forces_ram j)
    show f (j + 1) ≤ ram (j + 1) - 2
    omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V000.record record := by
  intro k
  show ram k - 2 ≤ 3 * Nat.factorial k - 2
  exact Nat.sub_le_sub_right (ram_le_factorial k) 2

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V000.record record :=
  ⟨4, by decide, by decide⟩

end SqueezeBench.Schur.Upper.V001
