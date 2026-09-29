import SqueezeBench.Problems.CapSet.Records.Upper.V006.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V005.Proof

/-! Record V006 for CapSet, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V006.lean`. -/

namespace SqueezeBench.CapSet.Upper.V006

open SqueezeBench Finset SqueezeBench.CapSet.Upper.V001

variable {m : ℕ}

-- Two translates `p - Y` and `p' - Y` of a cap `Y`, with `p ≠ p'`, share at most `|Y| / 2`
-- points: a common point `p - y = p' - y'` means `y' = y + (p' - p)`, and a cap meets its
-- nontrivial translate in at most half of its points (V004's `card_shift_inter`).
theorem card_inter_sub {Y : Finset (Fin m → ZMod 3)}
    (hY : ThreeAPFree (Y : Set (Fin m → ZMod 3))) {p p' : Fin m → ZMod 3} (hpp : p ≠ p') :
    2 * (Y.image (fun y => p - y) ∩ Y.image (fun y => p' - y)).card ≤ Y.card := by
  classical
  have hsub : Y.image (fun y => p - y) ∩ Y.image (fun y => p' - y)
      ⊆ (Y.filter (fun y => y + (p' - p) ∈ Y)).image (fun y => p - y) := by
    intro w hw
    rw [mem_inter, mem_image, mem_image] at hw
    obtain ⟨⟨y, hy, rfl⟩, ⟨y', hy', hyy'⟩⟩ := hw
    rw [mem_image]
    refine ⟨y, ?_, rfl⟩
    rw [mem_filter]
    refine ⟨hy, ?_⟩
    have : y + (p' - p) = y' := by linear_combination hyy'
    rw [this]; exact hy'
  have hcard := card_le_card hsub
  have hinj : ((Y.filter (fun y => y + (p' - p) ∈ Y)).image (fun y => p - y)).card
      = (Y.filter (fun y => y + (p' - p) ∈ Y)).card :=
    card_image_of_injective _ (fun a b hab => by simpa using hab)
  have hhalf := SqueezeBench.CapSet.Upper.V004.card_shift_inter hY (d := p' - p)
    (sub_ne_zero.mpr (Ne.symm hpp))
  omega

-- A point `p` outside the sumset `X + Y` gives a translate `p - Y` disjoint from `X`.
theorem disjoint_of_not_mem_add {X Y : Finset (Fin m → ZMod 3)} {p : Fin m → ZMod 3}
    (hp : p ∉ image₂ (· + ·) X Y) : Disjoint X (Y.image (fun y => p - y)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_image] at hx'
  obtain ⟨y, hy, hxy⟩ := hx'
  apply hp
  rw [mem_image₂]
  exact ⟨x, hx, y, hy, by rw [← hxy]; abel⟩

theorem card_image_sub (Y : Finset (Fin m → ZMod 3)) (p : Fin m → ZMod 3) :
    (Y.image (fun y => p - y)).card = Y.card :=
  card_image_of_injective _ (fun a b hab => by simpa using hab)

-- Two points missing from `X + Y`: `X` avoids the union of two translates of `-Y`, which
-- has at least `2|Y| - |Y|/2` points.
theorem two_missing {X Y : Finset (Fin m → ZMod 3)}
    (hY : ThreeAPFree (Y : Set (Fin m → ZMod 3))) {p p' : Fin m → ZMod 3} (hpp : p ≠ p')
    (hp : p ∉ image₂ (· + ·) X Y) (hp' : p' ∉ image₂ (· + ·) X Y) :
    X.card + 2 * Y.card ≤ 3 ^ m + Y.card / 2 := by
  classical
  have hdisj : Disjoint X (Y.image (fun y => p - y) ∪ Y.image (fun y => p' - y)) :=
    Finset.disjoint_union_right.mpr ⟨disjoint_of_not_mem_add hp, disjoint_of_not_mem_add hp'⟩
  have hcard := card_union_of_disjoint hdisj
  have hle : (X ∪ (Y.image (fun y => p - y) ∪ Y.image (fun y => p' - y))).card ≤ 3 ^ m := by
    calc _ ≤ (univ : Finset (Fin m → ZMod 3)).card := card_le_univ _
      _ = 3 ^ m := by simp
  have hun := card_union_add_card_inter (Y.image (fun y => p - y)) (Y.image (fun y => p' - y))
  have hc1 := card_image_sub Y p
  have hc2 := card_image_sub Y p'
  have hint := card_inter_sub hY hpp
  omega

-- Three points missing from `X + Y`: `X` avoids the union of three translates of `-Y`,
-- which has at least `3|Y| - 3 (|Y|/2)` points by inclusion–exclusion.
theorem three_missing {X Y : Finset (Fin m → ZMod 3)}
    (hY : ThreeAPFree (Y : Set (Fin m → ZMod 3))) {p p' p'' : Fin m → ZMod 3}
    (h12 : p ≠ p') (h13 : p ≠ p'') (h23 : p' ≠ p'')
    (hp : p ∉ image₂ (· + ·) X Y) (hp' : p' ∉ image₂ (· + ·) X Y)
    (hp'' : p'' ∉ image₂ (· + ·) X Y) :
    X.card + 3 * Y.card ≤ 3 ^ m + 3 * (Y.card / 2) := by
  classical
  have hdisj : Disjoint X (Y.image (fun y => p - y) ∪ Y.image (fun y => p' - y)
      ∪ Y.image (fun y => p'' - y)) :=
    Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr
      ⟨disjoint_of_not_mem_add hp, disjoint_of_not_mem_add hp'⟩, disjoint_of_not_mem_add hp''⟩
  have hcard := card_union_of_disjoint hdisj
  have hle : (X ∪ (Y.image (fun y => p - y) ∪ Y.image (fun y => p' - y)
      ∪ Y.image (fun y => p'' - y))).card ≤ 3 ^ m := by
    calc _ ≤ (univ : Finset (Fin m → ZMod 3)).card := card_le_univ _
      _ = 3 ^ m := by simp
  have hun12 := card_union_add_card_inter (Y.image (fun y => p - y)) (Y.image (fun y => p' - y))
  have hun3 := card_union_add_card_inter (Y.image (fun y => p - y) ∪ Y.image (fun y => p' - y))
    (Y.image (fun y => p'' - y))
  rw [union_inter_distrib_right] at hun3
  have hsub := card_union_le (Y.image (fun y => p - y) ∩ Y.image (fun y => p'' - y))
    (Y.image (fun y => p' - y) ∩ Y.image (fun y => p'' - y))
  have hc1 := card_image_sub Y p
  have hc2 := card_image_sub Y p'
  have hc3 := card_image_sub Y p''
  have hi12 := card_inter_sub hY h12
  have hi13 := card_inter_sub hY h13
  have hi23 := card_inter_sub hY h23
  omega

-- The sumset of two `4`-caps in `F₃²` misses at most one point: two missing points would
-- leave fewer than `4` points for the first cap.
theorem card_add_four_four {X Y : Finset (Fin 2 → ZMod 3)}
    (hY : ThreeAPFree (Y : Set (Fin 2 → ZMod 3)))
    (hXc : X.card = 4) (hYc : Y.card = 4) : 8 ≤ (image₂ (· + ·) X Y).card := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have h9 : (univ : Finset (Fin 2 → ZMod 3)).card = 9 := by simp
  have hsd := card_sdiff_add_card_eq_card (subset_univ (image₂ (· + ·) X Y))
  have h2 : 1 < ((univ : Finset (Fin 2 → ZMod 3)) \ image₂ (· + ·) X Y).card := by omega
  obtain ⟨p, hp, p', hp', hpp⟩ := one_lt_card.mp h2
  rw [mem_sdiff] at hp hp'
  have := two_missing (X := X) hY hpp hp.2 hp'.2
  norm_num at this
  omega

-- The sumset of a `4`-cap and a `3`-cap in `F₃²` misses at most two points.
theorem card_add_four_three {X Y : Finset (Fin 2 → ZMod 3)}
    (hY : ThreeAPFree (Y : Set (Fin 2 → ZMod 3)))
    (hXc : X.card = 4) (hYc : Y.card = 3) : 7 ≤ (image₂ (· + ·) X Y).card := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have h9 : (univ : Finset (Fin 2 → ZMod 3)).card = 9 := by simp
  have hsd := card_sdiff_add_card_eq_card (subset_univ (image₂ (· + ·) X Y))
  have h3 : 2 < ((univ : Finset (Fin 2 → ZMod 3)) \ image₂ (· + ·) X Y).card := by omega
  obtain ⟨p, hp, p', hp', p'', hp'', h12, h13, h23⟩ := two_lt_card.mp h3
  rw [mem_sdiff] at hp hp' hp''
  have := three_missing (X := X) hY h12 h13 h23 hp.2 hp'.2 hp''.2
  norm_num at this
  omega

-- The slice inequality with the whole sumset: for a line `{t, u, s}` of the last coordinate,
-- `-(S_t + S_s)` misses `S_u`, since `(x, t), (-(x+z), u), (z, s)` is a line.
theorem card_slice_add {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) {t u s : ZMod 3} (htu : t ≠ u)
    (hline : t + s = u + u) :
    (image₂ (· + ·) (slice A t) (slice A s)).card + (slice A u).card ≤ 3 ^ m := by
  classical
  have hdbl : ∀ v : ZMod 3, -v + -v = v := by decide
  have hsub : (image₂ (· + ·) (slice A t) (slice A s)).image (fun w => -w)
      ⊆ (univ : Finset (Fin m → ZMod 3)) \ slice A u := by
    intro y hy
    rw [mem_image] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [mem_image₂] at hw
    obtain ⟨x, hx, z, hz, rfl⟩ := hw
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
  have hcard : ((image₂ (· + ·) (slice A t) (slice A s)).image (fun w => -w)).card
      = (image₂ (· + ·) (slice A t) (slice A s)).card :=
    card_image_of_injective _ (fun a b hab => by simpa using hab)
  have h1 := card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_eq_card (subset_univ (slice A u))
  have h3 : (univ : Finset (Fin m → ZMod 3)).card = 3 ^ m := by simp
  omega

-- A `4`-slice `S_t` together with a slice `S_s` of size `3` or `4` on a line `{t, u, s}`,
-- with `|S_s| + |S_u| = 6`, is impossible: `|S_t + S_s| + |S_u| ≥ 10 > 9`.
theorem no_ten_aux {A : Finset (Fin 3 → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin 3 → ZMod 3))) {t u s : ZMod 3} (htu : t ≠ u)
    (hline : t + s = u + u) (ht : (slice A t).card = 4) (hs : 3 ≤ (slice A s).card)
    (hsu : 6 ≤ (slice A s).card + (slice A u).card) : False := by
  have h := card_slice_add hA htu hline
  have hcap := slice_threeAPFree s hA
  have hs4 : (slice A s).card ≤ 4 := SqueezeBench.CapSet.Upper.V002.cap_two hcap
  norm_num at h
  rcases Nat.lt_or_ge (slice A s).card 4 with h3 | h4
  · have hs3 : (slice A s).card = 3 := by omega
    have := card_add_four_three hcap ht hs3
    omega
  · have hs4' : (slice A s).card = 4 := by omega
    have := card_add_four_four hcap ht hs4'
    omega

-- The exact value `f 3 = 9`: a `10`-cap in `F₃³` would have a `4`-slice and, on some line
-- through it, a slice of size at least `3`.
theorem cap_three_nine {A : Finset (Fin 3 → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin 3 → ZMod 3))) : A.card ≤ 9 := by
  have h10 := SqueezeBench.CapSet.Upper.V005.cap_three hA
  by_contra hlt
  have hsum := card_slices A
  have h0 := SqueezeBench.CapSet.Upper.V002.cap_two (slice_threeAPFree 0 hA)
  have h1 := SqueezeBench.CapSet.Upper.V002.cap_two (slice_threeAPFree 1 hA)
  have h2 := SqueezeBench.CapSet.Upper.V002.cap_two (slice_threeAPFree 2 hA)
  rcases (by omega : (slice A 0).card = 4 ∨ (slice A 1).card = 4 ∨ (slice A 2).card = 4)
    with e | e | e
  · rcases (by omega : 3 ≤ (slice A 1).card ∨ 3 ≤ (slice A 2).card) with h | h
    · exact no_ten_aux hA (t := 0) (u := 2) (s := 1) (by decide) (by decide) e h (by omega)
    · exact no_ten_aux hA (t := 0) (u := 1) (s := 2) (by decide) (by decide) e h (by omega)
  · rcases (by omega : 3 ≤ (slice A 0).card ∨ 3 ≤ (slice A 2).card) with h | h
    · exact no_ten_aux hA (t := 1) (u := 2) (s := 0) (by decide) (by decide) e h (by omega)
    · exact no_ten_aux hA (t := 1) (u := 0) (s := 2) (by decide) (by decide) e h (by omega)
  · rcases (by omega : 3 ≤ (slice A 0).card ∨ 3 ≤ (slice A 1).card) with h | h
    · exact no_ten_aux hA (t := 2) (u := 1) (s := 0) (by decide) (by decide) e h (by omega)
    · exact no_ten_aux hA (t := 2) (u := 0) (s := 1) (by decide) (by decide) e h (by omega)

-- Unrolling `f (m+1) ≤ 3 * f m` (V003's `step_three`) from the exact base `f 3 = 9`.
theorem cap_card_le : ∀ m : ℕ, ∀ A : Finset (Fin (m + 3) → ZMod 3),
    ThreeAPFree (A : Set (Fin (m + 3) → ZMod 3)) → A.card ≤ 9 * 3 ^ m := by
  intro m
  induction m with
  | zero =>
    intro A hA
    simpa using cap_three_nine hA
  | succ k ih =>
    intro A hA
    have h := SqueezeBench.CapSet.Upper.V003.step_three (B := 9 * 3 ^ k) (fun S hS => ih S hS) hA
    have hp : 9 * 3 ^ (k + 1) = 3 * (9 * 3 ^ k) := by ring
    omega

theorem f_le (n : ℕ) (hn : 3 ≤ n) : SqueezeBench.CapSet.f n ≤ 3 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hnm : SqueezeBench.CapSet.nMin ≤ m + 3 := by simp [SqueezeBench.CapSet.nMin]
  have hlt : SqueezeBench.CapSet.f (m + 3) < 9 * 3 ^ m + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have := cap_card_le m A hAPF
    omega
  have hp : 3 ^ (m + 3 - 1) = 9 * 3 ^ m := by
    rw [show m + 3 - 1 = m + 2 from by omega]; ring
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
  · rw [show record n = 3 ^ (n - 1) from by
      simp only [record, if_neg (by omega : ¬ n < 2), if_neg (by omega : ¬ n < 3)]]
    exact f_le n h3

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V005.record record := by
  intro n
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [record, SqueezeBench.CapSet.Upper.V005.record]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show record (k + 3) = 9 * 3 ^ k from by
      simp only [record, if_neg (by omega : ¬ k + 3 < 2), if_neg (by omega : ¬ k + 3 < 3)]
      rw [show k + 3 - 1 = k + 2 from by omega]; ring]
    rw [show SqueezeBench.CapSet.Upper.V005.record (k + 3) = 10 * 3 ^ k from by
      simp only [SqueezeBench.CapSet.Upper.V005.record, if_neg (by omega : ¬ k + 3 < 2),
        if_neg (by omega : ¬ k + 3 < 3)]
      congr 1]
    omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V005.record record :=
  ⟨3, by simp [SqueezeBench.CapSet.nMin], by
    norm_num [record, SqueezeBench.CapSet.Upper.V005.record]⟩

end SqueezeBench.CapSet.Upper.V006
