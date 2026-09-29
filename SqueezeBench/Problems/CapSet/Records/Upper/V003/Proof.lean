import SqueezeBench.Problems.CapSet.Records.Upper.V003.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V002.Proof

/-! Record V003 for CapSet, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V003.lean`. -/

namespace SqueezeBench.CapSet.Upper.V003

open SqueezeBench Finset SqueezeBench.CapSet.Upper.V001

variable {m : ℕ}

-- The three slices of a cap are caps one dimension down, so `f (m+1) ≤ 3 * f m`.
theorem step_three {B : ℕ}
    (hB : ∀ S : Finset (Fin m → ZMod 3), ThreeAPFree (S : Set (Fin m → ZMod 3)) → S.card ≤ B)
    {A : Finset (Fin (m + 1) → ZMod 3)} (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) :
    A.card ≤ 3 * B := by
  have hsum := card_slices A
  have hB0 := hB _ (slice_threeAPFree 0 hA)
  have hB1 := hB _ (slice_threeAPFree 1 hA)
  have hB2 := hB _ (slice_threeAPFree 2 hA)
  omega

-- Unrolling `f (m+1) ≤ 3 * f m` from the exact base `f 2 = 4` of V002.
theorem cap_card_le : ∀ m : ℕ, ∀ A : Finset (Fin (m + 2) → ZMod 3),
    ThreeAPFree (A : Set (Fin (m + 2) → ZMod 3)) → A.card ≤ 4 * 3 ^ m := by
  intro m
  induction m with
  | zero =>
    intro A hA
    simpa using SqueezeBench.CapSet.Upper.V002.cap_two hA
  | succ k ih =>
    intro A hA
    have h := step_three (B := 4 * 3 ^ k) (fun S hS => ih S hS) hA
    have hp : 4 * 3 ^ (k + 1) = 3 * (4 * 3 ^ k) := by ring
    omega

theorem f_le (n : ℕ) (hn : 2 ≤ n) : SqueezeBench.CapSet.f n ≤ 4 * 3 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnm : SqueezeBench.CapSet.nMin ≤ m + 2 := by simp [SqueezeBench.CapSet.nMin]
  have hlt : SqueezeBench.CapSet.f (m + 2) < 4 * 3 ^ m + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have := cap_card_le m A hAPF
    omega
  simpa using hlt

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := by
  intro n
  simp only [record]
  split
  · exact SqueezeBench.CapSet.Upper.V001.f_le n
  · exact f_le n (by omega)

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V002.record record := by
  intro n
  simp only [record, SqueezeBench.CapSet.Upper.V002.record]
  split
  · exact le_refl _
  · rename_i h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hp : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
    have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    simp only [Nat.add_sub_cancel]
    omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V002.record record :=
  ⟨3, by simp [SqueezeBench.CapSet.nMin], by
    simp only [record, SqueezeBench.CapSet.Upper.V002.record]
    norm_num⟩

end SqueezeBench.CapSet.Upper.V003
