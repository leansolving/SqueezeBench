import SqueezeBench.Problems.Golomb.Records.Upper.V007.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V006.Proof

-- Golomb upper-bound record V007 — validity.
-- Each table entry is an explicit optimal ruler, given as a list and checked by the kernel with
-- `rulerCheck`: the marks are distinct, the length is a mark, every mark is at most the length,
-- and all pairwise sums `x + y` (`x` at or before `y`) are distinct. The last check keeps the
-- sums seen so far in a `Nat` bitset (`testBit`, `|||`, `<<<`, all GMP-accelerated in the
-- kernel), so it is quadratic in the number of marks where `decide` on `IsSidon` was quartic.
-- `sidonCheck_spec` proves by induction that a passing check gives the Sidon property: the
-- bitset represents the set of sums already inserted, each new sum is fresh, and a sum of
-- two later marks can never equal a sum involving an earlier mark. No search happens here.

namespace SqueezeBench.Golomb.Upper.V007

open SqueezeBench Finset

/-- Insert the sums `a + b`, `b ∈ bs`, into the bitset `mask`; `none` on a repeated sum. -/
def addSums (a : ℕ) : List ℕ → ℕ → Option ℕ
  | [], mask => some mask
  | b :: bs, mask =>
      if mask.testBit (a + b) then none else addSums a bs (mask ||| (1 <<< (a + b)))

/-- All sums `x + y` with `x` at or before `y` in the list are distinct and fresh for `mask`. -/
def sidonCheck : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: as, mask =>
      match addSums a (a :: as) mask with
      | none => false
      | some mask' => sidonCheck as mask'

/-- The ruler check: distinct marks, `L` a mark, every mark `≤ L`, all pairwise sums distinct. -/
def rulerCheck (l : List ℕ) (L : ℕ) : Bool :=
  decide l.Nodup && decide (L ∈ l) && l.all (fun x => decide (x ≤ L)) && sidonCheck l 0

/-- `mask` is the bitset of `T`. -/
def Repr (mask : ℕ) (T : Set ℕ) : Prop := ∀ t, mask.testBit t = true ↔ t ∈ T

theorem repr_zero : Repr 0 ∅ := by
  intro t; simp

theorem repr_insert {mask : ℕ} {T : Set ℕ} (h : Repr mask T) (s : ℕ) :
    Repr (mask ||| (1 <<< s)) (insert s T) := by
  intro t
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, Bool.or_eq_true, h,
    decide_eq_true_eq, Set.mem_insert_iff]
  tauto

/-- A successful `addSums` inserts exactly the fresh sums `a + b`. -/
theorem addSums_spec (a : ℕ) : ∀ (bs : List ℕ) {mask mask' : ℕ} {T : Set ℕ},
    Repr mask T → addSums a bs mask = some mask' →
    ∃ T' : Set ℕ, Repr mask' T' ∧ T ⊆ T' ∧ (∀ b ∈ bs, a + b ∉ T) ∧ (∀ b ∈ bs, a + b ∈ T')
  | [], mask, mask', T, hT, h => by
      simp only [addSums, Option.some.injEq] at h
      subst h
      exact ⟨T, hT, le_refl _, by simp, by simp⟩
  | b :: bs, mask, mask', T, hT, h => by
      simp only [addSums] at h
      split_ifs at h with hbit
      have hnot : a + b ∉ T := fun hmem => hbit ((hT _).mpr hmem)
      obtain ⟨T', hT', hsub, hfresh, hin⟩ := addSums_spec a bs (repr_insert hT (a + b)) h
      refine ⟨T', hT', fun t ht => hsub (Set.mem_insert_of_mem _ ht), ?_, ?_⟩
      · intro b' hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact hnot
        · exact fun hmem => hfresh b' hb' (Set.mem_insert_of_mem _ hmem)
      · intro b' hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact hsub (Set.mem_insert _ _)
        · exact hin b' hb'

/-- The Sidon property, stated on a list. -/
def SidonList (l : List ℕ) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, ∀ z ∈ l, ∀ w ∈ l, x + y = z + w → (x = z ∧ y = w) ∨ (x = w ∧ y = z)

/-- A passing `sidonCheck` gives the Sidon property, and no sum of two marks lies in `T`. -/
theorem sidonCheck_spec : ∀ (l : List ℕ) {mask : ℕ} {T : Set ℕ},
    Repr mask T → sidonCheck l mask = true →
    (∀ x ∈ l, ∀ y ∈ l, x + y ∉ T) ∧ SidonList l
  | [], mask, T, _, _ => ⟨by simp, by simp [SidonList]⟩
  | a :: as, mask, T, hT, h => by
      simp only [sidonCheck] at h
      split at h
      · exact absurd h (by simp)
      next mask' hsome =>
        obtain ⟨T', hT', hsub, hfresh, hin⟩ := addSums_spec a (a :: as) hT hsome
        obtain ⟨ihfresh, ihsidon⟩ := sidonCheck_spec as hT' h
        refine ⟨?_, ?_⟩
        · intro x hx y hy
          rcases List.mem_cons.mp hx with hxa | hx'
          · rw [hxa]; exact hfresh y hy
          · rcases List.mem_cons.mp hy with hya | hy'
            · rw [hya, add_comm]; exact hfresh x hx
            · exact fun hmem => ihfresh x hx' y hy' (hsub hmem)
        · intro x hx y hy z hz w hw hxyzw
          have key : ∀ u ∈ a :: as, ∀ v ∈ as, ∀ v' ∈ as, a + u ≠ v + v' :=
            fun u hu v hv v' hv' heq => ihfresh v hv v' hv' (heq ▸ hin u hu)
          rcases List.mem_cons.mp hx with hxa | hx' <;> rcases List.mem_cons.mp hy with hya | hy' <;>
            rcases List.mem_cons.mp hz with hza | hz' <;> rcases List.mem_cons.mp hw with hwa | hw'
          · omega
          · omega
          · omega
          · rw [hxa] at hxyzw; exact absurd hxyzw (key y hy z hz' w hw')
          · omega
          · omega
          · omega
          · rw [hxa] at hxyzw; exact absurd hxyzw (key y hy z hz' w hw')
          · omega
          · omega
          · omega
          · rw [hya, add_comm] at hxyzw; exact absurd hxyzw (key x hx z hz' w hw')
          · rw [hza] at hxyzw; exact absurd hxyzw.symm (key w hw x hx' y hy')
          · rw [hza] at hxyzw; exact absurd hxyzw.symm (key w hw x hx' y hy')
          · rw [hwa, add_comm z] at hxyzw; exact absurd hxyzw.symm (key z hz x hx' y hy')
          · exact ihsidon x hx' y hy' z hz' w hw' hxyzw

/-- A list passing `rulerCheck` with `m` marks and length `L` gives `f m ≤ L`. -/
theorem f_le_of_rulerCheck (l : List ℕ) (m L : ℕ) (hm : l.length = m)
    (h : rulerCheck l L = true) : f m ≤ L := by
  simp only [rulerCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hnodup, hL⟩, hle⟩, hcheck⟩ := h
  obtain ⟨_, hsidon⟩ := sidonCheck_spec l repr_zero hcheck
  have hm1 : nMin ≤ m := by
    rw [nMin_eq, ← hm]
    exact List.length_pos_of_mem hL
  refine f_le_of_mem hm1 ⟨l.toFinset, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hle x hx)
  · rw [List.toFinset_card_of_nodup hnodup, hm]
  · intro x hx y hy z hz w hw hxyzw
    rw [List.mem_toFinset] at hx hy hz hw
    exact hsidon x hx y hy z hz w hw hxyzw
  · exact List.mem_toFinset.mpr hL

-- The table entries: each optimal ruler, checked by the kernel.
theorem f18 : f 18 ≤ 216 :=
  f_le_of_rulerCheck
      [0, 2, 10, 22, 53, 56, 82, 83, 89, 98, 130, 148, 153, 167, 188, 192, 205, 216]
      18 216 rfl (by decide +kernel)

theorem f19 : f 19 ≤ 246 :=
  f_le_of_rulerCheck
      [0, 1, 6, 25, 32, 72, 100, 108, 120, 130, 153, 169, 187, 190, 204, 231, 233, 242, 246]
      19 246 rfl (by decide +kernel)

theorem f20 : f 20 ≤ 283 :=
  f_le_of_rulerCheck
      [0, 1, 8, 11, 68, 77, 94, 116, 121, 156, 158, 179, 194, 208, 212, 228, 240, 253, 259, 283]
      20 283 rfl (by decide +kernel)

theorem f21 : f 21 ≤ 333 :=
  f_le_of_rulerCheck
      [0, 2, 24, 56, 77, 82, 83, 95, 129, 144, 179, 186, 195, 255, 265, 285, 293, 296, 310, 329,
        333]
      21 333 rfl (by decide +kernel)

theorem f22 : f 22 ≤ 356 :=
  f_le_of_rulerCheck
      [0, 1, 9, 14, 43, 70, 106, 122, 124, 128, 159, 179, 204, 223, 253, 263, 270, 291, 330, 341,
        353, 356]
      22 356 rfl (by decide +kernel)

theorem f23 : f 23 ≤ 372 :=
  f_le_of_rulerCheck
      [0, 3, 7, 17, 61, 66, 91, 99, 114, 159, 171, 199, 200, 226, 235, 246, 277, 316, 329, 348,
        350, 366, 372]
      23 372 rfl (by decide +kernel)

theorem f24 : f 24 ≤ 425 :=
  f_le_of_rulerCheck
      [0, 9, 33, 37, 38, 97, 122, 129, 140, 142, 152, 191, 205, 208, 252, 278, 286, 326, 332, 353,
        368, 384, 403, 425]
      24 425 rfl (by decide +kernel)

theorem f25 : f 25 ≤ 480 :=
  f_le_of_rulerCheck
      [0, 12, 29, 39, 72, 91, 146, 157, 160, 161, 166, 191, 207, 214, 258, 290, 316, 354, 372,
        394, 396, 431, 459, 467, 480]
      25 480 rfl (by decide +kernel)

theorem f26 : f 26 ≤ 492 :=
  f_le_of_rulerCheck
      [0, 1, 33, 83, 104, 110, 124, 163, 185, 200, 203, 249, 251, 258, 314, 318, 343, 356, 386,
        430, 440, 456, 464, 475, 487, 492]
      26 492 rfl (by decide +kernel)

theorem f27 : f 27 ≤ 553 :=
  f_le_of_rulerCheck
      [0, 3, 15, 41, 66, 95, 97, 106, 142, 152, 220, 221, 225, 242, 295, 330, 338, 354, 382, 388,
        402, 415, 486, 504, 523, 546, 553]
      27 553 rfl (by decide +kernel)

theorem f28 : f 28 ≤ 585 :=
  f_le_of_rulerCheck
      [0, 3, 15, 41, 66, 95, 97, 106, 142, 152, 220, 221, 225, 242, 295, 330, 338, 354, 382, 388,
        402, 415, 486, 504, 523, 546, 553, 585]
      28 585 rfl (by decide +kernel)

theorem small_valid : UpperBoundHolds f small := by
  intro m
  by_cases h18 : m = 18
  · subst h18; exact f18
  by_cases h19 : m = 19
  · subst h19; exact f19
  by_cases h20 : m = 20
  · subst h20; exact f20
  by_cases h21 : m = 21
  · subst h21; exact f21
  by_cases h22 : m = 22
  · subst h22; exact f22
  by_cases h23 : m = 23
  · subst h23; exact f23
  by_cases h24 : m = 24
  · subst h24; exact f24
  by_cases h25 : m = 25
  · subst h25; exact f25
  by_cases h26 : m = 26
  · subst h26; exact f26
  by_cases h27 : m = 27
  · subst h27; exact f27
  by_cases h28 : m = 28
  · subst h28; exact f28
  have h : small m = SqueezeBench.Golomb.Upper.V006.record m := by
    simp only [small, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, if_false]
  rw [h]
  exact SqueezeBench.Golomb.Upper.V006.valid m

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Golomb.Upper.V006.valid small_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V006.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V006.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 28) (by decide)
    (by decide +kernel)

end SqueezeBench.Golomb.Upper.V007
