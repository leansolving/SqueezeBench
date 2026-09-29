import SqueezeBench.Problems.ExGirthFive.Records.Lower.V004.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V003.Proof

/-! Record V004 for ExGirthFive, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V004.lean`. -/

namespace SqueezeBench.ExGirthFive.Lower.V004

open Finset SimpleGraph SqueezeBench SqueezeBench.ExGirthFive

instance : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

-- Indices `0‥1018080` of a block are the points `(x, y)`, indices `1018081‥20401` the lines `y = a x + b`;
-- `co1` is the abscissa of a point and the slope of a line, `co2` the ordinate and the intercept.
-- For a line the index digit is `1009 + a`, and `(1009 : ZMod 1009) = 0`, so one formula serves both.
def co1 (i : ℕ) : ZMod 1009 := ((i % 2036162 / 1009 : ℕ) : ZMod 1009)

def co2 (i : ℕ) : ZMod 1009 := ((i % 2036162 % 1009 : ℕ) : ZMod 1009)

-- A point is adjacent to the lines through it, and nothing else.
def padj (i j : ℕ) : Prop :=
  (i % 2036162 < 1018081 ∧ 1018081 ≤ j % 2036162 ∧ co2 i = co1 j * co1 i + co2 j) ∨
  (j % 2036162 < 1018081 ∧ 1018081 ≤ i % 2036162 ∧ co2 j = co1 i * co1 j + co2 i)

instance : DecidableRel padj := fun i j => by unfold padj; infer_instance

theorem padj_symm {i j : ℕ} (h : padj i j) : padj j i := Or.symm h

-- Adjacent indices lie on opposite sides: one is a point, the other a line.
theorem padj_side {i j : ℕ} (h : padj i j) :
    (i % 2036162 < 1018081 ∧ 1018081 ≤ j % 2036162) ∨ (j % 2036162 < 1018081 ∧ 1018081 ≤ i % 2036162) := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

-- The incidence equation, read with `i` the point.
theorem padj_inc {i j : ℕ} (h : padj i j) (hi : i % 2036162 < 1018081) :
    co2 i = co1 j * co1 i + co2 j := by
  rcases h with ⟨-, -, he⟩ | ⟨-, h2, -⟩
  · exact he
  · exact absurd hi (by omega)

-- Both coordinates and the side determine the index inside a block.
theorem idx_eq {i j : ℕ} (h1 : co1 i = co1 j) (h2 : co2 i = co2 j)
    (hs : i % 2036162 < 1018081 ↔ j % 2036162 < 1018081) : i % 2036162 = j % 2036162 := by
  have e1 : (i % 2036162 / 1009) % 1009 = (j % 2036162 / 1009) % 1009 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have e2 : (i % 2036162 % 1009) % 1009 = (j % 2036162 % 1009) % 1009 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  omega

-- `⌊n/2036162⌋ ` disjoint copies of the incidence graph inside `Fin n`.
def planeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x.val / 2036162 = y.val / 2036162 ∧ padj x.val y.val
  symm := ⟨by rintro x y ⟨h1, h2⟩; exact ⟨h1.symm, padj_symm h2⟩⟩
  loopless := ⟨by
    rintro x ⟨-, h⟩
    rcases padj_side h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

instance (n : ℕ) : DecidableRel (planeGraph n).Adj :=
  fun x y => inferInstanceAs (Decidable (x.val / 2036162 = y.val / 2036162 ∧ padj x.val y.val))

-- The graph is bipartite between points and lines, so it has no triangle.
theorem planeGraph_cliqueFree (n : ℕ) : (planeGraph n).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  have h1 := padj_side hab.2
  have h2 := padj_side hac.2
  have h3 := padj_side hbc.2
  omega

-- Two points lie on at most one common line and two lines meet in at most one point.
theorem planeGraph_noTwo (n : ℕ) : NoTwoCommonNeighbours (planeGraph n) := by
  rintro x y u v hxy huv ⟨bxu, axu⟩ ⟨byu, ayu⟩ ⟨bxv, axv⟩ ⟨byv, ayv⟩
  have hx : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hu : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have sxu := padj_side axu
  have syu := padj_side ayu
  have sxv := padj_side axv
  have syv := padj_side ayv
  by_cases hxp : x.val % 2036162 < 1018081
  · -- `x` and `y` are points, `u` and `v` are lines through both of them
    have hup : 1018081 ≤ u.val % 2036162 := by omega
    have hvp : 1018081 ≤ v.val % 2036162 := by omega
    have hyp : y.val % 2036162 < 1018081 := by omega
    have e1 : co2 x.val = co1 u.val * co1 x.val + co2 u.val := padj_inc axu hxp
    have e2 : co2 y.val = co1 u.val * co1 y.val + co2 u.val := padj_inc ayu hyp
    have e3 : co2 x.val = co1 v.val * co1 x.val + co2 v.val := padj_inc axv hxp
    have e4 : co2 y.val = co1 v.val * co1 y.val + co2 v.val := padj_inc ayv hyp
    by_cases hc : co1 x.val = co1 y.val
    · have h2 : co2 x.val = co2 y.val := by linear_combination e1 - e2 + co1 u.val * hc
      have := idx_eq hc h2 (by omega)
      exact hx (by omega)
    · have key : co1 u.val * (co1 x.val - co1 y.val) = co1 v.val * (co1 x.val - co1 y.val) := by
        linear_combination e2 - e1 + e3 - e4
      have h1 : co1 u.val = co1 v.val := mul_right_cancel₀ (sub_ne_zero.mpr hc) key
      have h2 : co2 u.val = co2 v.val := by linear_combination e3 - e1 - co1 x.val * h1
      have := idx_eq h1 h2 (by omega)
      exact hu (by omega)
  · -- `x` and `y` are lines, `u` and `v` are points on both of them
    have hup : u.val % 2036162 < 1018081 := by omega
    have hvp : v.val % 2036162 < 1018081 := by omega
    have hyp : 1018081 ≤ y.val % 2036162 := by omega
    have e1 : co2 u.val = co1 x.val * co1 u.val + co2 x.val := padj_inc (padj_symm axu) hup
    have e2 : co2 u.val = co1 y.val * co1 u.val + co2 y.val := padj_inc (padj_symm ayu) hup
    have e3 : co2 v.val = co1 x.val * co1 v.val + co2 x.val := padj_inc (padj_symm axv) hvp
    have e4 : co2 v.val = co1 y.val * co1 v.val + co2 y.val := padj_inc (padj_symm ayv) hvp
    by_cases hc : co1 x.val = co1 y.val
    · have h2 : co2 x.val = co2 y.val := by linear_combination e2 - e1 - co1 u.val * hc
      have := idx_eq hc h2 (by omega)
      exact hx (by omega)
    · have key : (co1 x.val - co1 y.val) * co1 u.val = (co1 x.val - co1 y.val) * co1 v.val := by
        linear_combination e2 - e1 + e3 - e4
      have h1 : co1 u.val = co1 v.val := mul_left_cancel₀ (sub_ne_zero.mpr hc) key
      have h2 : co2 u.val = co2 v.val := by linear_combination e1 - e3 + co1 x.val * h1
      have := idx_eq h1 h2 (by omega)
      exact hu (by omega)

-- Vertex of index `i` (taken mod `n`, the identity on the indices used below).
def vv (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

-- One edge per block, slope, intercept and abscissa: the point `(x, a x + b)` on the line `(a, b)`.
def pt (k a b x : ℕ) : ℕ := 2036162 * k + 1009 * x + (a * x + b) % 1009

def ln (k a b : ℕ) : ℕ := 2036162 * k + 1018081 + 1009 * a + b

theorem plane_card (n : ℕ) (hn : 0 < n) : 1027243729 * (n / 2036162) ≤ #(planeGraph n).edgeFinset := by
  set S := (Finset.range (n / 2036162)) ×ˢ
    ((Finset.range 1009) ×ˢ ((Finset.range 1009) ×ˢ (Finset.range 1009))) with hS
  set F : ℕ × ℕ × ℕ × ℕ → Sym2 (Fin n) := fun q =>
    s(vv n hn (pt q.1 q.2.1 q.2.2.1 q.2.2.2), vv n hn (ln q.1 q.2.1 q.2.2.1)) with hF
  have hmem : ∀ q ∈ S, q.1 < n / 2036162 ∧ q.2.1 < 1009 ∧ q.2.2.1 < 1009 ∧ q.2.2.2 < 1009 := by
    rintro ⟨k, a, b, x⟩ hq
    simp only [hS, Finset.mem_product, Finset.mem_range] at hq
    exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2⟩
  -- the two indices of an edge, and where they sit inside their block
  have hbd : ∀ q ∈ S, pt q.1 q.2.1 q.2.2.1 q.2.2.2 < n ∧ ln q.1 q.2.1 q.2.2.1 < n ∧
      pt q.1 q.2.1 q.2.2.1 q.2.2.2 % 2036162 = 1009 * q.2.2.2 + (q.2.1 * q.2.2.2 + q.2.2.1) % 1009 ∧
      ln q.1 q.2.1 q.2.2.1 % 2036162 = 1018081 + 1009 * q.2.1 + q.2.2.1 ∧
      pt q.1 q.2.1 q.2.2.1 q.2.2.2 / 2036162 = q.1 ∧ ln q.1 q.2.1 q.2.2.1 / 2036162 = q.1 := by
    intro q hq
    obtain ⟨hk, ha, hb, hx⟩ := hmem q hq
    have hy : (q.2.1 * q.2.2.2 + q.2.2.1) % 1009 < 1009 := Nat.mod_lt _ (by norm_num)
    have hkn : 2036162 * q.1 + 2036162 ≤ n := by omega
    simp only [pt, ln]
    omega
  have hval : ∀ q ∈ S, (vv n hn (pt q.1 q.2.1 q.2.2.1 q.2.2.2)).val =
      pt q.1 q.2.1 q.2.2.1 q.2.2.2 ∧ (vv n hn (ln q.1 q.2.1 q.2.2.1)).val = ln q.1 q.2.1 q.2.2.1 := by
    intro q hq
    obtain ⟨h1, h2, -⟩ := hbd q hq
    exact ⟨Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2⟩
  have hsub : S.image F ⊆ (planeGraph n).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨q, hq, rfl⟩ := he
    obtain ⟨hk, ha, hb, hx⟩ := hmem q hq
    obtain ⟨hlt1, hlt2, hm1, hm2, hd1, hd2⟩ := hbd q hq
    obtain ⟨hv1, hv2⟩ := hval q hq
    have hy : (q.2.1 * q.2.2.2 + q.2.2.1) % 1009 < 1009 := Nat.mod_lt _ (by norm_num)
    simp only [hF, mem_edgeFinset, mem_edgeSet, planeGraph]
    refine ⟨by rw [hv1, hv2, hd1, hd2], Or.inl ⟨by rw [hv1]; omega, by rw [hv2]; omega, ?_⟩⟩
    have c1 : co1 (vv n hn (pt q.1 q.2.1 q.2.2.1 q.2.2.2)).val = ((q.2.2.2 : ℕ) : ZMod 1009) := by
      simp only [co1, hv1, hm1]
      congr 1
      omega
    have c2 : co2 (vv n hn (pt q.1 q.2.1 q.2.2.1 q.2.2.2)).val =
        (((q.2.1 * q.2.2.2 + q.2.2.1) % 1009 : ℕ) : ZMod 1009) := by
      simp only [co2, hv1, hm1]
      congr 1
      omega
    have c3 : co1 (vv n hn (ln q.1 q.2.1 q.2.2.1)).val = ((1009 + q.2.1 : ℕ) : ZMod 1009) := by
      simp only [co1, hv2, hm2]
      congr 1
      omega
    have c4 : co2 (vv n hn (ln q.1 q.2.1 q.2.2.1)).val = ((q.2.2.1 : ℕ) : ZMod 1009) := by
      simp only [co2, hv2, hm2]
      congr 1
      omega
    rw [c1, c2, c3, c4, ZMod.natCast_mod]
    push_cast
    rw [show (1009 : ZMod 1009) = 0 from by decide]
    ring
  have hinj : Set.InjOn F ↑S := by
    intro q hq q' hq' h
    have hq1 : q ∈ S := by simpa using hq
    have hq1' : q' ∈ S := by simpa using hq'
    obtain ⟨hk, ha, hb, hx⟩ := hmem q hq1
    obtain ⟨hk', ha', hb', hx'⟩ := hmem q' hq1'
    obtain ⟨hlt1, hlt2, hm1, hm2, -⟩ := hbd q hq1
    obtain ⟨hlt1', hlt2', hm1', hm2', -⟩ := hbd q' hq1'
    obtain ⟨hv1, hv2⟩ := hval q hq1
    obtain ⟨hv1', hv2'⟩ := hval q' hq1'
    have hy : (q.2.1 * q.2.2.2 + q.2.2.1) % 1009 < 1009 := Nat.mod_lt _ (by norm_num)
    have hy' : (q'.2.1 * q'.2.2.2 + q'.2.2.1) % 1009 < 1009 := Nat.mod_lt _ (by norm_num)
    have key : q.1 = q'.1 ∧ q.2.1 = q'.2.1 ∧ q.2.2.1 = q'.2.2.1 ∧ q.2.2.2 = q'.2.2.2 := by
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a1 := congrArg Fin.val h1
        have a2 := congrArg Fin.val h2
        rw [hv1, hv1'] at a1
        rw [hv2, hv2'] at a2
        simp only [pt, ln] at a1 a2
        omega
      · have a1 := congrArg Fin.val h1
        have a2 := congrArg Fin.val h2
        rw [hv1, hv2'] at a1
        rw [hv2, hv1'] at a2
        simp only [pt, ln] at a1 a2
        omega
    obtain ⟨k1, k2, k3, k4⟩ := key
    exact Prod.ext k1 (Prod.ext k2 (Prod.ext k3 k4))
  calc (1027243729 : ℕ) * (n / 2036162)
      = #(S.image F) := by
        rw [Finset.card_image_of_injOn hinj, hS]
        simp only [Finset.card_product, Finset.card_range]
        ring
    _ ≤ #(planeGraph n).edgeFinset := Finset.card_le_card hsub

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f blocks := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · exact le_trans (plane_card n hn)
      (le_f_of_cliqueFree_of_noTwoCommonNeighbours hn (planeGraph_cliqueFree n)
        (planeGraph_noTwo n))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V003.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V003.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V003.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 2036162) (by decide)
    (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V004
