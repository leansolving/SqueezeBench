import SqueezeBench.Problems.CapSet.Records.Upper.V002.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V001.Proof

/-! Record V002 for CapSet, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V002.lean`. -/

namespace SqueezeBench.CapSet.Upper.V002

open SqueezeBench Finset SqueezeBench.CapSet.Upper.V001

variable {m : ℕ}

-- The slice inequality of V001, for an arbitrary line `{t, u, s}` of the last coordinate:
-- translating the slice at `t` by a point of the slice at `s` and negating lands in the
-- complement of the slice at `u`.
theorem card_slice_pair {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) {t u s : ZMod 3} (htu : t ≠ u)
    (hline : t + s = u + u) {z : Fin m → ZMod 3} (hz : z ∈ slice A s) :
    (slice A t).card + (slice A u).card ≤ 3 ^ m := by
  classical
  have hdbl : ∀ v : ZMod 3, -v + -v = v := by decide
  have hsub : (slice A t).image (fun x => -(x + z))
      ⊆ (univ : Finset (Fin m → ZMod 3)) \ slice A u := by
    intro w hw
    simp only [mem_image] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [mem_sdiff]
    refine ⟨mem_univ _, ?_⟩
    intro hmem
    rw [V001.mem_slice] at hx hz hmem
    have hhalf : x + z = -(x + z) + -(x + z) := by
      funext i; simpa using (hdbl (x i + z i)).symm
    have := hA (mem_coe.mpr hx) (mem_coe.mpr hmem) (mem_coe.mpr hz) (snoc_line hhalf hline)
    have h01 := congrFun this (Fin.last m)
    simp only [Fin.snoc_last] at h01
    exact htu h01
  have hcard : ((slice A t).image (fun x => -(x + z))).card = (slice A t).card := by
    refine card_image_of_injective _ ?_
    intro a b hab
    simpa using hab
  have h1 := card_le_card hsub
  rw [hcard] at h1
  have h2 := Finset.card_sdiff_add_card_eq_card (subset_univ (slice A u))
  have h3 : (univ : Finset (Fin m → ZMod 3)).card = 3 ^ m := by simp
  omega

-- Either some slice is empty, and `A` is covered by the two remaining slices, or all three
-- are nonempty and every pair of slices fits inside `F₃^m`, so `2 |A| ≤ 3 · 3 ^ m`.
theorem step_half {B : ℕ}
    (hB : ∀ S : Finset (Fin m → ZMod 3), ThreeAPFree (S : Set (Fin m → ZMod 3)) → S.card ≤ B)
    {A : Finset (Fin (m + 1) → ZMod 3)} (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) :
    2 * A.card ≤ 3 * 3 ^ m ∨ A.card ≤ 2 * B := by
  classical
  have hsum := card_slices A
  have hB0 := hB _ (slice_threeAPFree 0 hA)
  have hB1 := hB _ (slice_threeAPFree 1 hA)
  have hB2 := hB _ (slice_threeAPFree 2 hA)
  rcases Finset.eq_empty_or_nonempty (slice A 0) with h | ⟨z0, hz0⟩
  · right; rw [h] at hsum; simp only [card_empty] at hsum; omega
  rcases Finset.eq_empty_or_nonempty (slice A 1) with h | ⟨z1, hz1⟩
  · right; rw [h] at hsum; simp only [card_empty] at hsum; omega
  rcases Finset.eq_empty_or_nonempty (slice A 2) with h | ⟨z2, hz2⟩
  · right; rw [h] at hsum; simp only [card_empty] at hsum; omega
  left
  have p01 := card_slice_pair hA (t := 0) (u := 1) (s := 2) (by decide) (by decide) hz2
  have p02 := card_slice_pair hA (t := 0) (u := 2) (s := 1) (by decide) (by decide) hz1
  have p12 := card_slice_pair hA (t := 1) (u := 2) (s := 0) (by decide) (by decide) hz0
  omega

-- The exact value `f 2 = 4`, from the three pairwise slice inequalities in `F₃¹`.
theorem cap_two {A : Finset (Fin 2 → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin 2 → ZMod 3))) : A.card ≤ 4 := by
  have hB : ∀ S : Finset (Fin 1 → ZMod 3),
      ThreeAPFree (S : Set (Fin 1 → ZMod 3)) → S.card ≤ 2 := by
    intro S hS
    have h := SqueezeBench.CapSet.Upper.V000.card_le_of_threeAPFree (m := 0) hS
    norm_num at h
    exact h
  rcases step_half hB hA with h | h
  · norm_num at h; omega
  · omega

-- Unrolling `|A| ≤ 3 ^ m + B` from the base `f 2 ≤ 4`.
theorem cap_card_le : ∀ m : ℕ, ∀ A : Finset (Fin (m + 2) → ZMod 3),
    ThreeAPFree (A : Set (Fin (m + 2) → ZMod 3)) → A.card ≤ (3 ^ (m + 2) - 1) / 2 := by
  intro m
  induction m with
  | zero =>
    intro A hA
    have h := cap_two hA
    norm_num
    omega
  | succ k ih =>
    intro A hA
    have h := step (B := (3 ^ (k + 2) - 1) / 2) (fun S hS => ih S hS) hA
    have hp : 3 ^ (k + 1 + 2) = 3 * 3 ^ (k + 2) := by ring
    have h1 : 1 ≤ 3 ^ (k + 2) := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem f_le (n : ℕ) (hn : 2 ≤ n) : SqueezeBench.CapSet.f n ≤ (3 ^ n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnm : SqueezeBench.CapSet.nMin ≤ m + 2 := by simp [SqueezeBench.CapSet.nMin]
  have hlt : SqueezeBench.CapSet.f (m + 2) < (3 ^ (m + 2) - 1) / 2 + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have := cap_card_le m A hAPF
    omega
  omega

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := by
  intro n
  simp only [record]
  split
  · exact SqueezeBench.CapSet.Upper.V001.f_le n
  · exact f_le n (by omega)

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V001.record record := by
  intro n
  simp only [record, SqueezeBench.CapSet.Upper.V001.record]
  split
  · exact le_refl _
  · refine Nat.div_le_div_right ?_
    exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V001.record record :=
  ⟨2, by simp [SqueezeBench.CapSet.nMin], by
    simp only [record, SqueezeBench.CapSet.Upper.V001.record]
    norm_num⟩

end SqueezeBench.CapSet.Upper.V002
