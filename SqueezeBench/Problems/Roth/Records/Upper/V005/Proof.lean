import SqueezeBench.Problems.Roth.Records.Upper.V005.Def
import SqueezeBench.Problems.Roth.Records.Upper.V004.Proof

/-! Record V005 for Roth, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V005.lean`. -/

namespace SqueezeBench.Roth.Upper.V005

/-! ### Windows

A 3-AP-free set meets any `m` consecutive integers in at most `r₃(m)` points
(`addRothNumber_Ico`). With the exact values already proved this is the main local tool. -/

theorem win {S : Finset ℕ} (hfree : ThreeAPFree (S : Set ℕ)) (a b : ℕ) :
    (S ∩ Finset.Ico a b).card ≤ rothNumberNat (b - a) := by
  rw [← addRothNumber_Ico]
  exact ThreeAPFree.le_addRothNumber
    (hfree.mono (by intro x hx; simp only [Finset.coe_inter, Set.mem_inter_iff] at hx; exact hx.1))
    Finset.inter_subset_right

theorem win_add {S : Finset ℕ} (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    (S ∩ Finset.Ico a b).card + (S ∩ Finset.Ico b c).card = (S ∩ Finset.Ico a c).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (Finset.Ico_disjoint_Ico_consecutive a b c))

theorem unit_le {S : Finset ℕ} (a b : ℕ) (hb : b = a + 1) : (S ∩ Finset.Ico a b).card ≤ 1 := by
  subst hb
  calc (S ∩ Finset.Ico a (a + 1)).card ≤ (Finset.Ico a (a + 1)).card :=
        Finset.card_le_card Finset.inter_subset_right
    _ = 1 := by simp

theorem unit_zero {S : Finset ℕ} (a b : ℕ) (hb : b = a + 1) (h : a ∉ S) :
    (S ∩ Finset.Ico a b).card = 0 := by
  subst hb
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter, Finset.mem_Ico] at hx
  have : x = a := by omega
  exact h (this ▸ hx.1)

-- The previous record bounds `rothNumberNat` itself.
theorem rbound (m : ℕ) : rothNumberNat m ≤ SqueezeBench.Roth.Upper.V004.record m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact le_trans (rothNumberNat_le 0) (Nat.zero_le _)
  · have h := SqueezeBench.Roth.Upper.V004.valid m
    rwa [SqueezeBench.Roth.f_of_le hm] at h

/-! ### Two more exact values, `r₃(10) ≤ 5` and `r₃(12) ≤ 6` -/

-- Six points in `[0, 10)`: at most four in `[0, 8)` and in `[2, 10)`, so `0, 1, 8, 9 ∈ S`;
-- then `2, 4, 5, 7 ∉ S`, so `S = {0, 1, 3, 6, 8, 9}`, which contains `0, 3, 6`.
theorem roth10 : rothNumberNat 10 ≤ 5 := by
  by_contra hcon
  obtain ⟨S, hts, hcard, hfree⟩ := rothNumberNat_spec 10
  have h6 : 6 ≤ S.card := by omega
  have hlt : ∀ x ∈ S, x < 10 := fun x hx => Finset.mem_range.mp (hts hx)
  have mid : ∀ {a b c : ℕ}, a ∈ S → b ∈ S → c ∈ S → a + c = b + b → a = b :=
    fun ha hb hc h => hfree (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
      (Finset.mem_coe.mpr hc) h
  have hS : S ∩ Finset.Ico 0 10 = S := by
    rw [Finset.inter_eq_left]
    intro x hx; rw [Finset.mem_Ico]; exact ⟨Nat.zero_le _, hlt x hx⟩
  have w08 := (win hfree 0 8).trans SqueezeBench.Roth.Upper.V004.roth8
  have w210 := (win hfree 2 10).trans SqueezeBench.Roth.Upper.V004.roth8
  have a1 := win_add (S := S) 0 8 10 (by norm_num) (by norm_num)
  have a2 := win_add (S := S) 0 2 10 (by norm_num) (by norm_num)
  have a3 := win_add (S := S) 8 9 10 (by norm_num) (by norm_num)
  have a4 := win_add (S := S) 0 1 2 (by norm_num) (by norm_num)
  rw [hS] at a1 a2
  have u8 := unit_le (S := S) 8 9 rfl
  have u9 := unit_le (S := S) 9 10 rfl
  have u0 := unit_le (S := S) 0 1 rfl
  have u1 := unit_le (S := S) 1 2 rfl
  have h8 : 8 ∈ S := by by_contra h; have := unit_zero (S := S) 8 9 rfl h; omega
  have h9 : 9 ∈ S := by by_contra h; have := unit_zero (S := S) 9 10 rfl h; omega
  have h0 : 0 ∈ S := by by_contra h; have := unit_zero (S := S) 0 1 rfl h; omega
  have h1 : 1 ∈ S := by by_contra h; have := unit_zero (S := S) 1 2 rfl h; omega
  have n2 : 2 ∉ S := fun h => absurd (mid h0 h1 h rfl) (by decide)
  have n7 : 7 ∉ S := fun h => absurd (mid h h8 h9 rfl) (by decide)
  have n4 : 4 ∉ S := fun h => absurd (mid h0 h h8 rfl) (by decide)
  have n5 : 5 ∉ S := fun h => absurd (mid h1 h h9 rfl) (by decide)
  have hsub : S ⊆ ({0, 1, 3, 6, 8, 9} : Finset ℕ) := by
    intro y hy
    have := hlt y hy
    have : y ≠ 2 := fun e => n2 (e ▸ hy)
    have : y ≠ 4 := fun e => n4 (e ▸ hy)
    have : y ≠ 5 := fun e => n5 (e ▸ hy)
    have : y ≠ 7 := fun e => n7 (e ▸ hy)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hSeq : S = ({0, 1, 3, 6, 8, 9} : Finset ℕ) :=
    Finset.eq_of_subset_of_card_le hsub (by
      have := Finset.card_le_card hsub
      have h : ({0, 1, 3, 6, 8, 9} : Finset ℕ).card = 6 := by decide
      omega)
  have m3 : (3:ℕ) ∈ S := by rw [hSeq]; decide
  have m6 : (6:ℕ) ∈ S := by rw [hSeq]; decide
  exact absurd (mid h0 m3 m6 rfl) (by decide)

-- Seven points in `[0, 12)`: at most four in `[0, 8)` and in `[4, 12)`, so three in `[0, 4)`
-- and three in `[8, 12)`, which forces `0, 3, 8, 11 ∈ S`; then `[4, 8)` is empty.
theorem roth12 : rothNumberNat 12 ≤ 6 := by
  by_contra hcon
  obtain ⟨S, hts, hcard, hfree⟩ := rothNumberNat_spec 12
  have h7 : 7 ≤ S.card := by omega
  have hlt : ∀ x ∈ S, x < 12 := fun x hx => Finset.mem_range.mp (hts hx)
  have mid : ∀ {a b c : ℕ}, a ∈ S → b ∈ S → c ∈ S → a + c = b + b → a = b :=
    fun ha hb hc h => hfree (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
      (Finset.mem_coe.mpr hc) h
  have hS : S ∩ Finset.Ico 0 12 = S := by
    rw [Finset.inter_eq_left]
    intro x hx; rw [Finset.mem_Ico]; exact ⟨Nat.zero_le _, hlt x hx⟩
  have w08 := (win hfree 0 8).trans SqueezeBench.Roth.Upper.V004.roth8
  have w412 := (win hfree 4 12).trans SqueezeBench.Roth.Upper.V004.roth8
  have w04 := (win hfree 0 4).trans
    ((rbound 4).trans (by decide : SqueezeBench.Roth.Upper.V004.record 4 ≤ 3))
  have w812 := (win hfree 8 12).trans
    ((rbound 4).trans (by decide : SqueezeBench.Roth.Upper.V004.record 4 ≤ 3))
  have a1 := win_add (S := S) 0 4 12 (by norm_num) (by norm_num)
  have a2 := win_add (S := S) 0 8 12 (by norm_num) (by norm_num)
  have a3 := win_add (S := S) 4 8 12 (by norm_num) (by norm_num)
  rw [hS] at a1 a2
  have b0 := win_add (S := S) 0 1 4 (by norm_num) (by norm_num)
  have b1 := win_add (S := S) 1 2 4 (by norm_num) (by norm_num)
  have b2 := win_add (S := S) 2 3 4 (by norm_num) (by norm_num)
  have c0 := win_add (S := S) 8 9 12 (by norm_num) (by norm_num)
  have c1 := win_add (S := S) 9 10 12 (by norm_num) (by norm_num)
  have c2 := win_add (S := S) 10 11 12 (by norm_num) (by norm_num)
  have u0 := unit_le (S := S) 0 1 rfl
  have u1 := unit_le (S := S) 1 2 rfl
  have u2 := unit_le (S := S) 2 3 rfl
  have u3 := unit_le (S := S) 3 4 rfl
  have u8 := unit_le (S := S) 8 9 rfl
  have u9 := unit_le (S := S) 9 10 rfl
  have u10 := unit_le (S := S) 10 11 rfl
  have u11 := unit_le (S := S) 11 12 rfl
  have h0 : 0 ∈ S := by
    by_contra h
    have := unit_zero (S := S) 0 1 rfl h
    have h1 : 1 ∈ S := by by_contra h'; have := unit_zero (S := S) 1 2 rfl h'; omega
    have h2 : 2 ∈ S := by by_contra h'; have := unit_zero (S := S) 2 3 rfl h'; omega
    have h3 : 3 ∈ S := by by_contra h'; have := unit_zero (S := S) 3 4 rfl h'; omega
    exact absurd (mid h1 h2 h3 rfl) (by decide)
  have h3 : 3 ∈ S := by
    by_contra h
    have := unit_zero (S := S) 3 4 rfl h
    have h1 : 1 ∈ S := by by_contra h'; have := unit_zero (S := S) 1 2 rfl h'; omega
    have h2 : 2 ∈ S := by by_contra h'; have := unit_zero (S := S) 2 3 rfl h'; omega
    exact absurd (mid h0 h1 h2 rfl) (by decide)
  have h8 : 8 ∈ S := by
    by_contra h
    have := unit_zero (S := S) 8 9 rfl h
    have h9 : 9 ∈ S := by by_contra h'; have := unit_zero (S := S) 9 10 rfl h'; omega
    have h10 : 10 ∈ S := by by_contra h'; have := unit_zero (S := S) 10 11 rfl h'; omega
    have h11 : 11 ∈ S := by by_contra h'; have := unit_zero (S := S) 11 12 rfl h'; omega
    exact absurd (mid h9 h10 h11 rfl) (by decide)
  have h11 : 11 ∈ S := by
    by_contra h
    have := unit_zero (S := S) 11 12 rfl h
    have h9 : 9 ∈ S := by by_contra h'; have := unit_zero (S := S) 9 10 rfl h'; omega
    have h10 : 10 ∈ S := by by_contra h'; have := unit_zero (S := S) 10 11 rfl h'; omega
    exact absurd (mid h8 h9 h10 rfl) (by decide)
  have n4 : 4 ∉ S := fun h => absurd (mid h0 h h8 rfl) (by decide)
  have n5 : 5 ∉ S := fun h => absurd (mid h h8 h11 rfl) (by decide)
  have n6 : 6 ∉ S := fun h => absurd (mid h0 h3 h rfl) (by decide)
  have n7 : 7 ∉ S := fun h => absurd (mid h3 h h11 rfl) (by decide)
  have hmid : S ∩ Finset.Ico 4 8 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, Finset.mem_Ico] at hx
    have : x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact n4 hx.1
    · exact n5 hx.1
    · exact n6 hx.1
    · exact n7 hx.1
  rw [hmid, Finset.card_empty] at a3
  omega

/-! ### The doubling recursion `r₃(2m+1) ≤ 2 r₃(m)` (Erdős–Turán) and `r₃(17) ≤ 8` -/

-- A 3-AP-free subset of `[0, 2m]` misses an endpoint, and so lies in `2m` consecutive
-- integers, or contains both endpoints and hence misses their midpoint `m`.
theorem roth_odd (m : ℕ) (hm : 1 ≤ m) : rothNumberNat (2 * m + 1) ≤ 2 * rothNumberNat m := by
  obtain ⟨S, hts, hcard, hfree⟩ := rothNumberNat_spec (2 * m + 1)
  rw [← hcard]
  have hlt : ∀ x ∈ S, x < 2 * m + 1 := fun x hx => Finset.mem_range.mp (hts hx)
  have hsub2 : rothNumberNat (2 * m) ≤ 2 * rothNumberNat m := by
    have := rothNumberNat_add_le m m
    rw [← two_mul] at this
    omega
  by_cases h0 : 0 ∈ S
  · by_cases h2 : 2 * m ∈ S
    · have hm' : m ∉ S := fun h => by
        have := hfree (Finset.mem_coe.mpr h0) (Finset.mem_coe.mpr h) (Finset.mem_coe.mpr h2)
          (by omega)
        omega
      have w1 := win hfree 0 m
      have w2 := win hfree (m + 1) (2 * m + 1)
      rw [Nat.sub_zero] at w1
      rw [show 2 * m + 1 - (m + 1) = m by omega] at w2
      have hsub : S ⊆ S ∩ Finset.Ico 0 m ∪ S ∩ Finset.Ico (m + 1) (2 * m + 1) := by
        intro x hx
        have := hlt x hx
        have hxm : x ≠ m := fun e => hm' (e ▸ hx)
        rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter, Finset.mem_Ico, Finset.mem_Ico]
        rcases Nat.lt_or_gt_of_ne hxm with h | h
        · exact Or.inl ⟨hx, Nat.zero_le _, h⟩
        · exact Or.inr ⟨hx, by omega, by omega⟩
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    · have hS : S ⊆ Finset.range (2 * m) := by
        intro x hx
        have := hlt x hx
        have : x ≠ 2 * m := fun e => h2 (e ▸ hx)
        rw [Finset.mem_range]; omega
      have h1 := ThreeAPFree.le_addRothNumber hfree hS
      rw [← rothNumberNat_def] at h1
      omega
  · have hS : S ⊆ Finset.Ico 1 (2 * m + 1) := by
      intro x hx
      have := hlt x hx
      have : x ≠ 0 := fun e => h0 (e ▸ hx)
      rw [Finset.mem_Ico]; omega
    have h1 := ThreeAPFree.le_addRothNumber hfree hS
    rw [addRothNumber_Ico, show 2 * m + 1 - 1 = 2 * m by omega] at h1
    omega

theorem roth17 : rothNumberNat 17 ≤ 8 := by
  have h := roth_odd 8 (by norm_num)
  have := SqueezeBench.Roth.Upper.V004.roth8
  simp only [show 2 * 8 + 1 = 17 from rfl] at h
  omega

/-! ### `r₃(n) ≤ ⌈n/2⌉` for `n ≥ 8`, `n ≠ 14` -/

-- Blocks of `8` (`r₃ ≤ 4`) with a remainder block of `10`, `12`, `13` or `22` for the residues
-- `2, 4, 5, 6 (mod 8)`; the other residues are the previous record.
theorem half_valid (n : ℕ) (h8 : 8 ≤ n) (h14 : n ≠ 14) : rothNumberNat n ≤ (n + 1) / 2 := by
  have step := SqueezeBench.Roth.Upper.V004.step
  have r13 : rothNumberNat 13 ≤ 7 := by
    have : rothNumberNat 13 ≤ rothNumberNat 12 + rothNumberNat 1 := rothNumberNat_add_le 12 1
    have := rbound 1
    have h1 : SqueezeBench.Roth.Upper.V004.record 1 = 1 := by decide
    have := roth12
    omega
  have r22 : rothNumberNat 22 ≤ 11 := by
    have : rothNumberNat 22 ≤ rothNumberNat 10 + rothNumberNat 12 := rothNumberNat_add_le 10 12
    have := roth10
    have := roth12
    omega
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 8 ∧ n = 8 * q + t :=
    ⟨n / 8, n % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 8).symm⟩
  interval_cases t
  · have := step q 0; have := rbound 0
    have h0 : SqueezeBench.Roth.Upper.V004.record 0 = 0 := by decide
    omega
  · have := step q 1; have := rbound 1
    have h1 : SqueezeBench.Roth.Upper.V004.record 1 = 1 := by decide
    omega
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have := step q' 10
    rw [show 8 * (q' + 1) + 2 = 8 * q' + 10 by ring]
    have := roth10
    omega
  · have := step q 3; have := rbound 3
    have h3 : SqueezeBench.Roth.Upper.V004.record 3 = 2 := by decide
    omega
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have := step q' 12
    rw [show 8 * (q' + 1) + 4 = 8 * q' + 12 by ring]
    have := roth12
    omega
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have := step q' 13
    rw [show 8 * (q' + 1) + 5 = 8 * q' + 13 by ring]
    omega
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
    have := step q' 22
    rw [show 8 * (q' + 2) + 6 = 8 * q' + 22 by ring]
    omega
  · have := step q 7; have := rbound 7
    have h7 : SqueezeBench.Roth.Upper.V004.record 7 = 4 := by decide
    omega

/-! ### Moser's count: a 3-AP-free set of size `t` has at least `3t - 7` pairwise sums

Enumerate the set as `a 0 < a 1 < … < a (t-1)`. The sums `a i + a (i+1)` and `a i + a (i+2)`
interleave strictly, giving `2t - 3` values (the *chain*). For each `i ≤ t - 5`, one of
`a i + a (i+3)`, `a i + a (i+4)` lies outside the chain: `a i + a (i+3)` sits strictly between
`a i + a (i+2)` and `a (i+1) + a (i+3)`, so in the chain it must equal `a (i+1) + a (i+2)`;
then `a i + a (i+4)` sits strictly between that value and `a (i+2) + a (i+4)`, and either
chain value there would complete a three-term progression. These extra sums increase with
`i`, so they contribute `t - 4` further values. (L. Moser, *On non-averaging sets of
integers*, Canad. J. Math. 5 (1953), 245–252.) -/

-- Sums of two distinct elements of `A`.
def sums (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 < p.2)).image (fun p => p.1 + p.2)

theorem mem_sums {A : Finset ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x < y) :
    x + y ∈ sums A := by
  simp only [sums, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨(x, y), ⟨⟨hx, hy⟩, hxy⟩, rfl⟩

theorem sums_spec {A : Finset ℕ} {s : ℕ} (hs : s ∈ sums A) :
    ∃ x ∈ A, ∃ y ∈ A, x < y ∧ s = x + y := by
  simp only [sums, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hs
  obtain ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩ := hs
  exact ⟨x, hx, y, hy, hxy, rfl⟩

-- The chain: sums of neighbours and of next-to-neighbours in the increasing enumeration.
def chain (t : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (t - 1)).image (fun i => a i + a (i + 1)) ∪
    (Finset.range (t - 2)).image (fun i => a i + a (i + 2))

-- One extra sum per index, chosen outside the chain.
def extra (t : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ :=
  if a i + a (i + 3) ∈ chain t a then a i + a (i + 4) else a i + a (i + 3)

theorem mem_chain {t : ℕ} {a : ℕ → ℕ} {y : ℕ} :
    y ∈ chain t a ↔
      (∃ i, i < t - 1 ∧ a i + a (i + 1) = y) ∨ (∃ i, i < t - 2 ∧ a i + a (i + 2) = y) := by
  simp [chain, Finset.mem_union, Finset.mem_image, Finset.mem_range]

theorem hle_of_mono {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j) :
    ∀ i j, i ≤ j → j < t → a i ≤ a j := by
  intro i j hij hj
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (hmono i j h hj).le

-- If `a i + a (i+3)` is a chain element, it is the neighbour sum `a (i+1) + a (i+2)`.
theorem between₁ {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j) {i : ℕ}
    (hi : i + 3 < t) (h : a i + a (i + 3) ∈ chain t a) :
    a i + a (i + 3) = a (i + 1) + a (i + 2) := by
  have hle := hle_of_mono hmono
  rcases mem_chain.mp h with ⟨j, hj, hjy⟩ | ⟨j, hj, hjy⟩
  · rcases lt_trichotomy j (i + 1) with hlt | heq | hgt
    · have h1 := hle j i (by omega) (by omega)
      have h2 := hle (j + 1) (i + 1) (by omega) (by omega)
      have h3 := hmono (i + 1) (i + 3) (by omega) hi
      omega
    · have e1 : a j = a (i + 1) := by rw [heq]
      have e2 : a (j + 1) = a (i + 2) := by rw [show j + 1 = i + 2 by omega]
      omega
    · have h1 := hle (i + 2) j (by omega) (by omega)
      have h2 := hle (i + 3) (j + 1) (by omega) (by omega)
      have h3 := hmono i (i + 2) (by omega) (by omega)
      omega
  · rcases le_or_gt j i with hji | hij
    · have h1 := hle j i hji (by omega)
      have h2 := hle (j + 2) (i + 2) (by omega) (by omega)
      have h3 := hmono (i + 2) (i + 3) (by omega) hi
      omega
    · have h1 := hle (i + 1) j (by omega) (by omega)
      have h2 := hle (i + 3) (j + 2) (by omega) (by omega)
      have h3 := hmono i (i + 1) (by omega) (by omega)
      omega

-- If `a i + a (i+3)` is the neighbour sum, then `a i + a (i+4)` is outside the chain:
-- either position would complete a three-term progression.
theorem between₂ {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j)
    (hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) {i : ℕ}
    (hi : i + 4 < t) (hE : a i + a (i + 3) = a (i + 1) + a (i + 2)) :
    a i + a (i + 4) ∉ chain t a := by
  have hle := hle_of_mono hmono
  intro h
  rcases mem_chain.mp h with ⟨j, hj, hjy⟩ | ⟨j, hj, hjy⟩
  · rcases lt_trichotomy j (i + 2) with hlt | heq | hgt
    · have h1 := hle j (i + 1) (by omega) (by omega)
      have h2 := hle (j + 1) (i + 2) (by omega) (by omega)
      have h3 := hmono (i + 3) (i + 4) (by omega) hi
      omega
    · have e1 : a j = a (i + 2) := by rw [heq]
      have e2 : a (j + 1) = a (i + 3) := by rw [show j + 1 = i + 3 by omega]
      have := hfree (i + 1) (i + 3) (i + 4) (by omega) (by omega) hi (by omega)
      omega
    · have h1 := hle (i + 3) j (by omega) (by omega)
      have h2 := hle (i + 4) (j + 1) (by omega) (by omega)
      have h3 := hmono i (i + 3) (by omega) (by omega)
      omega
  · rcases lt_trichotomy j (i + 1) with hlt | heq | hgt
    · have h1 := hle j i (by omega) (by omega)
      have h2 := hle (j + 2) (i + 2) (by omega) (by omega)
      have h3 := hmono (i + 2) (i + 4) (by omega) hi
      omega
    · have e1 : a j = a (i + 1) := by rw [heq]
      have e2 : a (j + 2) = a (i + 3) := by rw [show j + 2 = i + 3 by omega]
      have := hfree (i + 2) (i + 3) (i + 4) (by omega) (by omega) hi (by omega)
      omega
    · have h1 := hle (i + 2) j (by omega) (by omega)
      have h2 := hle (i + 4) (j + 2) (by omega) (by omega)
      have h3 := hmono i (i + 2) (by omega) (by omega)
      omega

theorem extra_not_mem {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j)
    (hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j) {i : ℕ}
    (hi : i + 4 < t) : extra t a i ∉ chain t a := by
  unfold extra
  split_ifs with h
  · exact between₂ hmono hfree hi (between₁ hmono (by omega) h)
  · exact h

theorem extra_ge {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j) {i : ℕ}
    (hi : i + 4 < t) : a i + a (i + 3) ≤ extra t a i := by
  unfold extra
  split_ifs
  · have := hmono (i + 3) (i + 4) (by omega) hi; omega
  · exact le_rfl

theorem extra_le {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j) {i : ℕ}
    (hi : i + 4 < t) : extra t a i ≤ a i + a (i + 4) := by
  unfold extra
  split_ifs
  · exact le_rfl
  · have := hmono (i + 3) (i + 4) (by omega) hi; omega

theorem extra_mono {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j) {i j : ℕ}
    (hij : i < j) (hj : j + 4 < t) : extra t a i < extra t a j := by
  have hle := hle_of_mono hmono
  have h1 := extra_le hmono (i := i) (by omega)
  have h2 := extra_ge hmono hj
  have h3 := hmono i (i + 1) (by omega) (by omega)
  have h4 := hle (i + 1) j (by omega) (by omega)
  have h5 := hle (i + 4) (j + 3) (by omega) (by omega)
  omega

theorem chain_card {t : ℕ} {a : ℕ → ℕ} (hmono : ∀ i j, i < j → j < t → a i < a j) :
    (chain t a).card = (t - 1) + (t - 2) := by
  have hle := hle_of_mono hmono
  unfold chain
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn, Finset.card_image_of_injOn,
    Finset.card_range, Finset.card_range]
  · intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := hmono i j hlt (by omega); have := hmono (i + 2) (j + 2) (by omega) (by omega); omega
    · exact heq
    · have := hmono j i hgt (by omega); have := hmono (j + 2) (i + 2) (by omega) (by omega); omega
  · intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := hmono i j hlt (by omega); have := hmono (i + 1) (j + 1) (by omega) (by omega); omega
    · exact heq
    · have := hmono j i hgt (by omega); have := hmono (j + 1) (i + 1) (by omega) (by omega); omega
  · rw [Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_image] at hy hy'
    obtain ⟨j, hj, rfl⟩ := hy
    obtain ⟨i, hi, hij⟩ := hy'
    rw [Finset.mem_range] at hi hj
    rcases le_or_gt j i with h | h
    · have h1 := hle j i h (by omega)
      have h2 := hle (j + 1) (i + 1) (by omega) (by omega)
      have h3 := hmono (i + 1) (i + 2) (by omega) (by omega)
      omega
    · have h1 := hle (i + 1) j (by omega) (by omega)
      have h2 := hle (i + 2) (j + 1) (by omega) (by omega)
      have h3 := hmono i (i + 1) (by omega) (by omega)
      omega

-- Moser's count in index form.
theorem moser_index (t : ℕ) (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < t → a i < a j)
    (hfree : ∀ i j k, i < t → j < t → k < t → a i + a k = a j + a j → i = j)
    (D : Finset ℕ) (hD : ∀ i j, i < j → j < t → a i + a j ∈ D) :
    3 * t ≤ D.card + 7 := by
  have hsub : chain t a ∪ (Finset.range (t - 4)).image (extra t a) ⊆ D := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · rcases mem_chain.mp h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact hD i (i + 1) (by omega) (by omega)
      · exact hD i (i + 2) (by omega) (by omega)
    · rw [Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [Finset.mem_range] at hi
      unfold extra
      split_ifs
      · exact hD i (i + 4) (by omega) (by omega)
      · exact hD i (i + 3) (by omega) (by omega)
  have hdisj : Disjoint (chain t a) ((Finset.range (t - 4)).image (extra t a)) := by
    rw [Finset.disjoint_right]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    exact extra_not_mem hmono hfree (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, chain_card hmono, Finset.card_image_of_injOn,
    Finset.card_range] at hcard
  · omega
  · intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := extra_mono hmono hlt (by omega); omega
    · exact heq
    · have := extra_mono hmono hgt (by omega); omega

-- Moser's count for a 3-AP-free finset, via its increasing enumeration.
theorem moser_sums (A : Finset ℕ) (hA : ThreeAPFree (A : Set ℕ)) :
    3 * A.card ≤ (sums A).card + 7 := by
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
  exact moser_index t a hmono hfree (sums A)
    (fun i j hij hj => mem_sums (hmem i (by omega)) (hmem j hj) (hmono i j hij hj))

-- The midpoints of the pairwise sums of a parity class of a 3-AP-free `S ⊆ [0, n)` are
-- distinct integers below `n` outside `S`.
theorem key (n : ℕ) (S : Finset ℕ) (hlt : ∀ x ∈ S, x < n) (hfree : ThreeAPFree (S : Set ℕ))
    (A : Finset ℕ) (hAS : A ⊆ S) (r : ℕ) (hpar : ∀ x ∈ A, x % 2 = r) :
    S.card + (sums A).card ≤ n := by
  have hM : ((sums A).image (fun s => s / 2)).card = (sums A).card := by
    apply Finset.card_image_of_injOn
    intro s hs s' hs' h
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := sums_spec hs
    obtain ⟨x', hx', y', hy', hxy', rfl⟩ := sums_spec hs'
    have := hpar x hx; have := hpar y hy; have := hpar x' hx'; have := hpar y' hy'
    simp only at h
    omega
  have hdisj : Disjoint S ((sums A).image (fun s => s / 2)) := by
    rw [Finset.disjoint_right]
    intro z hz hzS
    rw [Finset.mem_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := sums_spec hs
    have := hpar x hx; have := hpar y hy
    have heq : x + y = (x + y) / 2 + (x + y) / 2 := by omega
    have := hfree (Finset.mem_coe.mpr (hAS hx)) (Finset.mem_coe.mpr hzS)
      (Finset.mem_coe.mpr (hAS hy)) heq
    omega
  have hsub : S ∪ (sums A).image (fun s => s / 2) ⊆ Finset.range n := by
    intro z hz
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hz with h | h
    · exact hlt z h
    · rw [Finset.mem_image] at h
      obtain ⟨s, hs, rfl⟩ := h
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := sums_spec hs
      have := hlt x (hAS hx); have := hlt y (hAS hy)
      omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hM, Finset.card_range] at this
  exact this

-- `k + 3e ≤ n + 7` for both parity classes, with `e₀ + e₁ = k`, bounds `k` by `moser n`.
theorem moser_arith {n k e₀ e₁ : ℕ} (h₀ : k + 3 * e₀ ≤ n + 7) (h₁ : k + 3 * e₁ ≤ n + 7)
    (hs : e₀ + e₁ = k) : k ≤ max (2 * ((n + 7) / 5)) (2 * ((n + 3) / 5) + 1) := by
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
  · apply le_max_of_le_left
    rcases le_total e₁ e₀ with h | h <;> omega
  · apply le_max_of_le_right
    rcases le_total e₁ e₀ with h | h <;> omega

theorem moser_valid (n : ℕ) : rothNumberNat n ≤ moser n := by
  obtain ⟨S, hts, hcard, hfree⟩ := rothNumberNat_spec n
  have hlt : ∀ x ∈ S, x < n := fun x hx => Finset.mem_range.mp (hts hx)
  have hsub₀ : S.filter (fun x => x % 2 = 0) ⊆ S := Finset.filter_subset _ _
  have hsub₁ : S.filter (fun x => ¬ x % 2 = 0) ⊆ S := Finset.filter_subset _ _
  have h₀ := key n S hlt hfree _ hsub₀ 0 (fun x hx => (Finset.mem_filter.mp hx).2)
  have h₁ := key n S hlt hfree _ hsub₁ 1
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)
  have m₀ := moser_sums _ (hfree.mono (Finset.coe_subset.mpr hsub₀))
  have m₁ := moser_sums _ (hfree.mono (Finset.coe_subset.mpr hsub₁))
  have hsplit : (S.filter (fun x => x % 2 = 0)).card
      + (S.filter (fun x => ¬ (x % 2 = 0))).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun x => x % 2 = 0)
  rw [← hcard]
  exact moser_arith (by omega) (by omega) hsplit

/-! ### The obligations -/

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f v := by
  intro n
  have h0 := SqueezeBench.Roth.Upper.V003.f_le_roth n
  refine le_trans h0 (le_min ?_ (moser_valid n))
  unfold half
  split_ifs with h
  · exact rothNumberNat_le n
  · exact half_valid n (by omega) (by omega)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.patch_valid' (SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V004.valid v_valid)
    (le_trans (SqueezeBench.Roth.Upper.V003.f_le_roth 17) roth17)

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V004.record record :=
  SqueezeBench.ImprovesUpper.trans SqueezeBench.minWith_improves
    (SqueezeBench.patch_improves' (by decide))

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V004.record record :=
  ⟨100, by decide, by decide⟩

end SqueezeBench.Roth.Upper.V005
