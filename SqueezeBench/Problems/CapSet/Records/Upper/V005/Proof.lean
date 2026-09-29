import SqueezeBench.Problems.CapSet.Records.Upper.V005.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V004.Proof

/-! Record V005 for CapSet, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V005.lean`. -/

namespace SqueezeBench.CapSet.Upper.V005

open SqueezeBench Finset

-- V004's bound at the single point `n = 3`: a cap in `F₃³` has at most `10` points.
theorem cap_three {A : Finset (Fin 3 → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin 3 → ZMod 3))) : A.card ≤ 10 := by
  have h := SqueezeBench.CapSet.le_f_of_threeAPFree (by simp [SqueezeBench.CapSet.nMin]) hA
  have h4 := SqueezeBench.CapSet.Upper.V004.valid 3
  rw [show SqueezeBench.CapSet.Upper.V004.record 3 = 10 from by
    norm_num [SqueezeBench.CapSet.Upper.V004.record]] at h4
  omega

-- Unrolling `f (m+1) ≤ 3 * f m` (V003's `step_three`) from that base.
theorem cap_card_le : ∀ m : ℕ, ∀ A : Finset (Fin (m + 3) → ZMod 3),
    ThreeAPFree (A : Set (Fin (m + 3) → ZMod 3)) → A.card ≤ 10 * 3 ^ m := by
  intro m
  induction m with
  | zero =>
    intro A hA
    simpa using cap_three hA
  | succ k ih =>
    intro A hA
    have h := SqueezeBench.CapSet.Upper.V003.step_three (B := 10 * 3 ^ k) (fun S hS => ih S hS) hA
    have hp : 10 * 3 ^ (k + 1) = 3 * (10 * 3 ^ k) := by ring
    omega

theorem f_le (n : ℕ) (hn : 3 ≤ n) : SqueezeBench.CapSet.f n ≤ 10 * 3 ^ (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnm : SqueezeBench.CapSet.nMin ≤ m + 3 := by simp [SqueezeBench.CapSet.nMin]
  have hlt : SqueezeBench.CapSet.f (m + 3) < 10 * 3 ^ m + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have := cap_card_le m A hAPF
    omega
  simpa using hlt

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := by
  intro n
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [show record n = (3 ^ n + 1) / 2 from by simp only [record, if_pos h]]
    exact SqueezeBench.CapSet.Upper.V001.f_le n
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    rw [show record 2 = 4 from by norm_num [record]]
    simpa using SqueezeBench.CapSet.Upper.V003.f_le 2 (by norm_num)
  · rw [show record n = 10 * 3 ^ (n - 3) from by
      simp only [record, if_neg (by omega : ¬ n < 2), if_neg (by omega : ¬ n < 3)]]
    exact f_le n h3

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V004.record record := by
  intro n
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [record, SqueezeBench.CapSet.Upper.V004.record]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show record (k + 3) = 10 * 3 ^ k from by
      simp only [record, if_neg (by omega : ¬ k + 3 < 2), if_neg (by omega : ¬ k + 3 < 3)]
      congr 1]
    rw [show SqueezeBench.CapSet.Upper.V004.record (k + 3) = 2 * 3 ^ (k + 3) / 5 from by
      simp only [SqueezeBench.CapSet.Upper.V004.record, if_neg (by omega : ¬ k + 3 < 2),
        if_neg (by omega : ¬ k + 3 < 3)]]
    have hp : 2 * 3 ^ (k + 3) = 54 * 3 ^ k := by ring
    rw [hp]
    omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V004.record record :=
  ⟨4, by simp [SqueezeBench.CapSet.nMin], by
    norm_num [record, SqueezeBench.CapSet.Upper.V004.record]⟩

end SqueezeBench.CapSet.Upper.V005
