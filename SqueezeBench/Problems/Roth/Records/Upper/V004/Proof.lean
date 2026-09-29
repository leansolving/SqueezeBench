import SqueezeBench.Problems.Roth.Records.Upper.V004.Def
import SqueezeBench.Problems.Roth.Records.Upper.V003.Proof

/-! Record V004 for Roth, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V004.lean`. -/

namespace SqueezeBench.Roth.Upper.V004

-- A 3-element subset of a 4-element set is the 4-element set minus one of its points.
theorem eq_sdiff_singleton {A T : Finset ℕ} (hAT : A ⊆ T) (hT : T.card = 4) (hA : A.card = 3) :
    ∃ x ∈ T, A = T \ {x} := by
  have hc : (T \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAT]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
  have hxT : x ∈ T := by
    have : x ∈ T \ A := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp this).1
  exact ⟨x, hxT, by rw [← hx, Finset.sdiff_sdiff_eq_self hAT]⟩

-- `r₃(8) ≤ 4`. Suppose `S ⊆ [0,8)` is 3-AP-free with `|S| ≥ 5`. The V002 count
-- `|S| + 2 |A_r| ≤ 11` on each parity class forces `|S| = 5` and `{|A₀|, |A₁|} = {2, 3}`.
-- The class of size 3 is a 3-AP-free 3-subset of a 4-term progression, so it omits its second
-- or its third term; its three pairwise midpoints then lie outside `S`, which pins `S` down to
-- five explicit points, and those always contain a 3-AP.
theorem roth8 : rothNumberNat 8 ≤ 4 := by
  by_contra hcon
  obtain ⟨S, hts, hcard, hfree⟩ := rothNumberNat_spec 8
  have h5 : 5 ≤ S.card := by omega
  have hlt : ∀ x ∈ S, x < 8 := fun x hx => Finset.mem_range.mp (hts hx)
  have mid : ∀ {a b c : ℕ}, a ∈ S → b ∈ S → c ∈ S → a + c = b + b → a = b :=
    fun ha hb hc h => hfree (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
      (Finset.mem_coe.mpr hc) h
  set A := S.filter (fun x => x % 2 = 0) with hAdef
  set B := S.filter (fun x => ¬ (x % 2 = 0)) with hBdef
  have hA := SqueezeBench.Roth.Upper.V002.key 8 S hlt hfree A (Finset.filter_subset _ _) 0
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have hB := SqueezeBench.Roth.Upper.V002.key 8 S hlt hfree B (Finset.filter_subset _ _) 1
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)
  have hsplit : A.card + B.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun x => x % 2 = 0)
  have hcard5 : S.card = 5 := by omega
  have hAT : A ⊆ ({0, 2, 4, 6} : Finset ℕ) := by
    intro x hx
    have h1 := hlt x (Finset.mem_filter.mp hx).1
    have h2 := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hBT : B ⊆ ({1, 3, 5, 7} : Finset ℕ) := by
    intro x hx
    have h1 := hlt x (Finset.mem_filter.mp hx).1
    have h2 := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  -- from a three-element class `C = {p, q, r}` whose midpoints are excluded, `S` is forced
  have force : ∀ p q r : ℕ, p ∈ S → q ∈ S → r ∈ S → ∀ m₁ m₂ m₃ : ℕ,
      p + q = m₁ + m₁ → p + r = m₂ + m₂ → q + r = m₃ + m₃ → p ≠ m₁ → p ≠ m₂ → q ≠ m₃ →
      ∀ y ∈ S, y ≠ m₁ ∧ y ≠ m₂ ∧ y ≠ m₃ := by
    intro p q r hp hq hr m₁ m₂ m₃ e₁ e₂ e₃ n₁ n₂ n₃ y hy
    refine ⟨fun h => n₁ (mid hp (h ▸ hy) hq e₁), fun h => n₂ (mid hp (h ▸ hy) hr e₂),
      fun h => n₃ (mid hq (h ▸ hy) hr e₃)⟩
  have hAcard : A.card = 3 ∨ B.card = 3 := by omega
  rcases hAcard with h3 | h3
  · obtain ⟨x, hxT, hxe⟩ := eq_sdiff_singleton hAT (by decide) h3
    have hx4 : x = 0 ∨ x = 2 ∨ x = 4 ∨ x = 6 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxT
    have hmem : ∀ z : ℕ, z ∈ ({0, 2, 4, 6} : Finset ℕ) \ {x} → z ∈ S := by
      intro z hz; exact (Finset.mem_filter.mp (hxe ▸ hz)).1
    rcases hx4 with rfl | rfl | rfl | rfl
    · exact absurd (mid (hmem 2 (by decide)) (hmem 4 (by decide)) (hmem 6 (by decide)) rfl)
        (by decide)
    · -- A = {0, 4, 6}; midpoints 2, 3, 5 are excluded, so S = {0, 1, 4, 6, 7} and 1,4,7 is a 3-AP
      have hf := force 0 4 6 (hmem 0 (by decide)) (hmem 4 (by decide)) (hmem 6 (by decide))
        2 3 5 rfl rfl rfl (by decide) (by decide) (by decide)
      have hsub : S ⊆ ({0, 1, 4, 6, 7} : Finset ℕ) := by
        intro y hy
        obtain ⟨n₁, n₂, n₃⟩ := hf y hy
        have := hlt y hy
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hSeq : S = ({0, 1, 4, 6, 7} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard5]; decide)
      have m₁ : (1:ℕ) ∈ S := by rw [hSeq]; decide
      have m₂ : (4:ℕ) ∈ S := by rw [hSeq]; decide
      have m₃ : (7:ℕ) ∈ S := by rw [hSeq]; decide
      exact absurd (mid m₁ m₂ m₃ rfl) (by decide)
    · -- A = {0, 2, 6}; midpoints 1, 3, 4 are excluded, so S = {0, 2, 5, 6, 7} and 5,6,7 is a 3-AP
      have hf := force 0 2 6 (hmem 0 (by decide)) (hmem 2 (by decide)) (hmem 6 (by decide))
        1 3 4 rfl rfl rfl (by decide) (by decide) (by decide)
      have hsub : S ⊆ ({0, 2, 5, 6, 7} : Finset ℕ) := by
        intro y hy
        obtain ⟨n₁, n₂, n₃⟩ := hf y hy
        have := hlt y hy
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hSeq : S = ({0, 2, 5, 6, 7} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard5]; decide)
      have m₁ : (5:ℕ) ∈ S := by rw [hSeq]; decide
      have m₂ : (6:ℕ) ∈ S := by rw [hSeq]; decide
      have m₃ : (7:ℕ) ∈ S := by rw [hSeq]; decide
      exact absurd (mid m₁ m₂ m₃ rfl) (by decide)
    · exact absurd (mid (hmem 0 (by decide)) (hmem 2 (by decide)) (hmem 4 (by decide)) rfl)
        (by decide)
  · obtain ⟨x, hxT, hxe⟩ := eq_sdiff_singleton hBT (by decide) h3
    have hx4 : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxT
    have hmem : ∀ z : ℕ, z ∈ ({1, 3, 5, 7} : Finset ℕ) \ {x} → z ∈ S := by
      intro z hz; exact (Finset.mem_filter.mp (hxe ▸ hz)).1
    rcases hx4 with rfl | rfl | rfl | rfl
    · exact absurd (mid (hmem 3 (by decide)) (hmem 5 (by decide)) (hmem 7 (by decide)) rfl)
        (by decide)
    · -- B = {1, 5, 7}; midpoints 3, 4, 6 are excluded, so S = {0, 1, 2, 5, 7} and 0,1,2 is a 3-AP
      have hf := force 1 5 7 (hmem 1 (by decide)) (hmem 5 (by decide)) (hmem 7 (by decide))
        3 4 6 rfl rfl rfl (by decide) (by decide) (by decide)
      have hsub : S ⊆ ({0, 1, 2, 5, 7} : Finset ℕ) := by
        intro y hy
        obtain ⟨n₁, n₂, n₃⟩ := hf y hy
        have := hlt y hy
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hSeq : S = ({0, 1, 2, 5, 7} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard5]; decide)
      have m₁ : (0:ℕ) ∈ S := by rw [hSeq]; decide
      have m₂ : (1:ℕ) ∈ S := by rw [hSeq]; decide
      have m₃ : (2:ℕ) ∈ S := by rw [hSeq]; decide
      exact absurd (mid m₁ m₂ m₃ rfl) (by decide)
    · -- B = {1, 3, 7}; midpoints 2, 4, 5 are excluded, so S = {0, 1, 3, 6, 7} and 0,3,6 is a 3-AP
      have hf := force 1 3 7 (hmem 1 (by decide)) (hmem 3 (by decide)) (hmem 7 (by decide))
        2 4 5 rfl rfl rfl (by decide) (by decide) (by decide)
      have hsub : S ⊆ ({0, 1, 3, 6, 7} : Finset ℕ) := by
        intro y hy
        obtain ⟨n₁, n₂, n₃⟩ := hf y hy
        have := hlt y hy
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hSeq : S = ({0, 1, 3, 6, 7} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcard5]; decide)
      have m₁ : (0:ℕ) ∈ S := by rw [hSeq]; decide
      have m₂ : (3:ℕ) ∈ S := by rw [hSeq]; decide
      have m₃ : (6:ℕ) ∈ S := by rw [hSeq]; decide
      exact absurd (mid m₁ m₂ m₃ rfl) (by decide)
    · exact absurd (mid (hmem 1 (by decide)) (hmem 3 (by decide)) (hmem 5 (by decide)) rfl)
        (by decide)

-- Subadditivity of `rothNumberNat`, iterated on blocks of eight.
theorem step (q t : ℕ) : rothNumberNat (8 * q + t) ≤ 4 * q + rothNumberNat t := by
  induction q with
  | zero => simp
  | succ q ih =>
      have he : 8 * (q + 1) + t = 8 + (8 * q + t) := by ring
      rw [he]
      calc rothNumberNat (8 + (8 * q + t))
          ≤ rothNumberNat 8 + rothNumberNat (8 * q + t) := rothNumberNat_add_le _ _
        _ ≤ 4 + (4 * q + rothNumberNat t) := Nat.add_le_add roth8 ih
        _ = 4 * (q + 1) + rothNumberNat t := by ring

theorem roth_le_prev (m : ℕ) : rothNumberNat m ≤ SqueezeBench.Roth.Upper.V003.record m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact le_trans (rothNumberNat_le 0) (Nat.zero_le _)
  · have h := SqueezeBench.Roth.Upper.V003.valid m
    rwa [SqueezeBench.Roth.f_of_le hm] at h

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f v := by
  intro n
  have h0 : SqueezeBench.Roth.f n ≤ rothNumberNat n :=
    SqueezeBench.Roth.Upper.V003.f_le_roth n
  have he : 8 * (n / 8) + n % 8 = n := Nat.div_add_mod' n 8 ▸ by omega
  have h1 : rothNumberNat n ≤ 4 * (n / 8) + rothNumberNat (n % 8) := by
    have hs := step (n / 8) (n % 8)
    rwa [he] at hs
  exact le_trans h0 (le_trans h1 (Nat.add_le_add_left (roth_le_prev (n % 8)) _))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V003.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V003.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V003.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 8) (by decide) (by decide)

end SqueezeBench.Roth.Upper.V004
