import SqueezeBench.Problems.CapSet.Records.Upper.V004.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V003.Proof

/-! Record V004 for CapSet, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V004.lean`. -/

namespace SqueezeBench.CapSet.Upper.V004

open SqueezeBench Finset SqueezeBench.CapSet.Upper.V001

variable {m : ℕ}

-- The subset step of V002's pair inequality, isolated so that two points of the slice at `s`
-- can be used at once: translating the slice at `t` by a point of the slice at `s` and
-- negating lands in the complement of the slice at `u`.
theorem slice_image_subset {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) {t u s : ZMod 3} (htu : t ≠ u)
    (hline : t + s = u + u) {z : Fin m → ZMod 3} (hz : z ∈ slice A s) :
    (slice A t).image (fun x => -(x + z)) ⊆ (univ : Finset (Fin m → ZMod 3)) \ slice A u := by
  classical
  have hdbl : ∀ v : ZMod 3, -v + -v = v := by decide
  intro y hy
  simp only [mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
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

-- A cap meets a nontrivial translate of itself in at most half of its points: if `x` and
-- `x + d` both lie in `T` then `x + d + d` does not, `{x, x + d, x + d + d}` being a line.
theorem card_shift_inter {T : Finset (Fin m → ZMod 3)}
    (hT : ThreeAPFree (T : Set (Fin m → ZMod 3))) {d : Fin m → ZMod 3} (hd : d ≠ 0) :
    2 * (T.filter (fun x => x + d ∈ T)).card ≤ T.card := by
  classical
  have hsub : (T.filter (fun x => x + d ∈ T)).image (fun x => x + d)
      ⊆ T \ T.filter (fun x => x + d ∈ T) := by
    intro y hy
    simp only [mem_image, mem_filter] at hy
    obtain ⟨x, ⟨hx, hxd⟩, rfl⟩ := hy
    rw [mem_sdiff, mem_filter]
    refine ⟨hxd, ?_⟩
    rintro ⟨-, h2⟩
    have hl : x + (x + d + d) = (x + d) + (x + d) := by ring
    have hxx := hT (mem_coe.mpr hx) (mem_coe.mpr hxd) (mem_coe.mpr h2) hl
    exact hd (by linear_combination -hxx)
  have hcard : ((T.filter (fun x => x + d ∈ T)).image (fun x => x + d)).card
      = (T.filter (fun x => x + d ∈ T)).card :=
    card_image_of_injective _ (fun a b hab => by simpa using hab)
  have h1 := card_le_card hsub
  rw [hcard] at h1
  have h2 := Finset.card_sdiff_add_card_eq_card (filter_subset (fun x => x + d ∈ T) T)
  omega

-- The sharpened pair inequality: with two distinct points of the slice at `s`, the slice at
-- `t` is translated twice, and the union of the two translates has at least `3/2` of its
-- points because a cap meets a translate of itself in at most half of its points.
theorem card_slice_pair_two {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) {t u s : ZMod 3} (htu : t ≠ u)
    (hline : t + s = u + u) {z w : Fin m → ZMod 3} (hz : z ∈ slice A s) (hw : w ∈ slice A s)
    (hzw : z ≠ w) :
    3 * (slice A t).card + 2 * (slice A u).card ≤ 2 * 3 ^ m := by
  classical
  have hinj1 : Function.Injective (fun x : Fin m → ZMod 3 => -(x + z)) :=
    fun a b hab => by simpa using hab
  have hinj2 : Function.Injective (fun x : Fin m → ZMod 3 => -(x + w)) :=
    fun a b hab => by simpa using hab
  have hsub : (slice A t).image (fun x => -(x + z)) ∪ (slice A t).image (fun x => -(x + w))
      ⊆ (univ : Finset (Fin m → ZMod 3)) \ slice A u :=
    union_subset (slice_image_subset hA htu hline hz) (slice_image_subset hA htu hline hw)
  have hIsub : (slice A t).image (fun x => -(x + z)) ∩ (slice A t).image (fun x => -(x + w))
      ⊆ ((slice A t).filter (fun x => x + (z - w) ∈ slice A t)).image (fun x => -(x + z)) := by
    intro p hp
    rw [mem_inter] at hp
    simp only [mem_image] at hp ⊢
    obtain ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩ := hp
    refine ⟨x, ?_, hxp⟩
    rw [mem_filter]
    refine ⟨hx, ?_⟩
    have h' : x + z = y + w := by
      have h := hxp.trans hyp.symm
      linear_combination -h
    have hxy : x + (z - w) = y := by linear_combination h'
    rw [hxy]; exact hy
  have hIcard : ((slice A t).image (fun x => -(x + z))
        ∩ (slice A t).image (fun x => -(x + w))).card
      ≤ ((slice A t).filter (fun x => x + (z - w) ∈ slice A t)).card := by
    calc ((slice A t).image (fun x => -(x + z))
          ∩ (slice A t).image (fun x => -(x + w))).card
        ≤ (((slice A t).filter (fun x => x + (z - w) ∈ slice A t)).image
            (fun x => -(x + z))).card := card_le_card hIsub
      _ = _ := card_image_of_injective _ hinj1
  have hc1 : ((slice A t).image (fun x => -(x + z))).card = (slice A t).card :=
    card_image_of_injective _ hinj1
  have hc2 : ((slice A t).image (fun x => -(x + w))).card = (slice A t).card :=
    card_image_of_injective _ hinj2
  have hun := card_union_add_card_inter ((slice A t).image (fun x => -(x + z)))
    ((slice A t).image (fun x => -(x + w)))
  have hle := card_le_card hsub
  have hsd := Finset.card_sdiff_add_card_eq_card (subset_univ (slice A u))
  have h3 : (univ : Finset (Fin m → ZMod 3)).card = 3 ^ m := by simp
  have hhalf := card_shift_inter (slice_threeAPFree t hA) (d := z - w) (sub_ne_zero.mpr hzw)
  rw [hc1, hc2] at hun
  omega

-- The recurrence: with every slice of size at least two the six sharpened pair inequalities
-- add up to `10 |A| ≤ 12 · 3^m`; a slice of size one leaves `|A| ≤ 3^m + 1` by V002's pair
-- inequality; an empty slice leaves `|A| ≤ 2 B`.
theorem step_five {B : ℕ}
    (hB : ∀ S : Finset (Fin m → ZMod 3), ThreeAPFree (S : Set (Fin m → ZMod 3)) → S.card ≤ B)
    {A : Finset (Fin (m + 1) → ZMod 3)} (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) :
    5 * A.card ≤ 6 * 3 ^ m ∨ A.card ≤ 3 ^ m + 1 ∨ A.card ≤ 2 * B := by
  classical
  have hsum := card_slices A
  have hB0 := hB _ (slice_threeAPFree 0 hA)
  have hB1 := hB _ (slice_threeAPFree 1 hA)
  have hB2 := hB _ (slice_threeAPFree 2 hA)
  rcases Finset.eq_empty_or_nonempty (slice A 0) with h | ⟨y0, hy0⟩
  · right; right; rw [h] at hsum; simp only [card_empty] at hsum; omega
  rcases Finset.eq_empty_or_nonempty (slice A 1) with h | ⟨y1, hy1⟩
  · right; right; rw [h] at hsum; simp only [card_empty] at hsum; omega
  rcases Finset.eq_empty_or_nonempty (slice A 2) with h | ⟨y2, hy2⟩
  · right; right; rw [h] at hsum; simp only [card_empty] at hsum; omega
  have q01 := SqueezeBench.CapSet.Upper.V002.card_slice_pair hA (t := 0) (u := 1) (s := 2)
    (by decide) (by decide) hy2
  have q02 := SqueezeBench.CapSet.Upper.V002.card_slice_pair hA (t := 0) (u := 2) (s := 1)
    (by decide) (by decide) hy1
  have q12 := SqueezeBench.CapSet.Upper.V002.card_slice_pair hA (t := 1) (u := 2) (s := 0)
    (by decide) (by decide) hy0
  by_cases hbig : 1 < (slice A 0).card ∧ 1 < (slice A 1).card ∧ 1 < (slice A 2).card
  · obtain ⟨z0, hz0, w0, hw0, hzw0⟩ := Finset.one_lt_card.mp hbig.1
    obtain ⟨z1, hz1, w1, hw1, hzw1⟩ := Finset.one_lt_card.mp hbig.2.1
    obtain ⟨z2, hz2, w2, hw2, hzw2⟩ := Finset.one_lt_card.mp hbig.2.2
    left
    have p01 := card_slice_pair_two hA (t := 0) (u := 1) (s := 2) (by decide) (by decide)
      hz2 hw2 hzw2
    have p10 := card_slice_pair_two hA (t := 1) (u := 0) (s := 2) (by decide) (by decide)
      hz2 hw2 hzw2
    have p02 := card_slice_pair_two hA (t := 0) (u := 2) (s := 1) (by decide) (by decide)
      hz1 hw1 hzw1
    have p20 := card_slice_pair_two hA (t := 2) (u := 0) (s := 1) (by decide) (by decide)
      hz1 hw1 hzw1
    have p12 := card_slice_pair_two hA (t := 1) (u := 2) (s := 0) (by decide) (by decide)
      hz0 hw0 hzw0
    have p21 := card_slice_pair_two hA (t := 2) (u := 1) (s := 0) (by decide) (by decide)
      hz0 hw0 hzw0
    omega
  · right; left
    have h0 := Finset.card_pos.mpr ⟨y0, hy0⟩
    have h1 := Finset.card_pos.mpr ⟨y1, hy1⟩
    have h2 := Finset.card_pos.mpr ⟨y2, hy2⟩
    simp only [not_and_or, not_lt] at hbig
    omega

-- Unrolling the recurrence from `f 2 ≤ 4`, whose first step already gives `f 3 ≤ 10`.
theorem cap_card_le : ∀ m : ℕ, ∀ A : Finset (Fin (m + 3) → ZMod 3),
    ThreeAPFree (A : Set (Fin (m + 3) → ZMod 3)) → A.card ≤ 2 * 3 ^ (m + 3) / 5 := by
  intro m
  induction m with
  | zero =>
    intro A hA
    have h := step_five (m := 2) (B := 4)
      (fun S hS => SqueezeBench.CapSet.Upper.V002.cap_two hS) hA
    norm_num at h ⊢
    omega
  | succ k ih =>
    intro A hA
    have h := step_five (m := k + 3) (B := 2 * 3 ^ (k + 3) / 5) (fun S hS => ih S hS) hA
    have hp : 3 ^ (k + 1 + 3) = 3 * 3 ^ (k + 3) := by ring
    have hbig : 27 ≤ 3 ^ (k + 3) := by
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hp]
    omega

theorem f_le (n : ℕ) (hn : 3 ≤ n) : SqueezeBench.CapSet.f n ≤ 2 * 3 ^ n / 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnm : SqueezeBench.CapSet.nMin ≤ m + 3 := by simp [SqueezeBench.CapSet.nMin]
  have hlt : SqueezeBench.CapSet.f (m + 3) < 2 * 3 ^ (m + 3) / 5 + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have := cap_card_le m A hAPF
    omega
  omega

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := by
  intro n
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [show record n = (3 ^ n + 1) / 2 from by simp only [record, if_pos h]]
    exact SqueezeBench.CapSet.Upper.V001.f_le n
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    rw [show record 2 = 4 from by norm_num [record]]
    simpa using SqueezeBench.CapSet.Upper.V003.f_le 2 (by norm_num)
  · rw [show record n = 2 * 3 ^ n / 5 from by
      simp only [record, if_neg (by omega : ¬ n < 2), if_neg (by omega : ¬ n < 3)]]
    exact f_le n h3

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V003.record record := by
  intro n
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [record, SqueezeBench.CapSet.Upper.V003.record]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show record (k + 3) = 2 * 3 ^ (k + 3) / 5 from by
      simp only [record, if_neg (by omega : ¬ k + 3 < 2), if_neg (by omega : ¬ k + 3 < 3)]]
    rw [show SqueezeBench.CapSet.Upper.V003.record (k + 3) = 4 * 3 ^ (k + 1) from by
      simp only [SqueezeBench.CapSet.Upper.V003.record, if_neg (by omega : ¬ k + 3 < 2)]
      congr 1]
    have hp : 3 ^ (k + 3) = 9 * 3 ^ (k + 1) := by ring
    omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V003.record record :=
  ⟨3, by simp [SqueezeBench.CapSet.nMin], by
    norm_num [record, SqueezeBench.CapSet.Upper.V003.record]⟩

end SqueezeBench.CapSet.Upper.V004
