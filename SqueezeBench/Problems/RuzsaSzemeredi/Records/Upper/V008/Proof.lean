import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V008.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V007.Proof

/-! Record V008 for RuzsaSzemeredi, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V008.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V008

open Finset SimpleGraph
open SqueezeBench.RuzsaSzemeredi.Upper.V006 (trianglesAt degree_eq card_inter_neighborFinset_le)


-- The bisection keeps `lo² ≤ d < hi²` and ends with `hi = lo + 1` when the fuel covers `hi − lo`.
theorem isqrtAux_spec (d : ℕ) : ∀ fuel lo hi, lo * lo ≤ d → d < hi * hi → lo < hi →
    hi ≤ lo + fuel + 1 →
    isqrtAux d fuel lo hi * isqrtAux d fuel lo hi ≤ d ∧
      d < (isqrtAux d fuel lo hi + 1) * (isqrtAux d fuel lo hi + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi h1 h2 h3 h4
    have : hi = lo + 1 := by omega
    subst this
    simpa [isqrtAux] using ⟨h1, h2⟩
  | succ fuel ih =>
    intro lo hi h1 h2 h3 h4
    simp only [isqrtAux]
    split
    · rename_i hmid
      have : hi = lo + 1 := by omega
      subst this
      exact ⟨h1, h2⟩
    · rename_i hmid
      split
      · rename_i hle
        exact ih _ _ hle h2 (by omega) (by omega)
      · rename_i hlt
        exact ih _ _ h1 (by omega) (by omega) (by omega)

theorem isqrt_spec (d : ℕ) : isqrt d * isqrt d ≤ d ∧ d < (isqrt d + 1) * (isqrt d + 1) :=
  isqrtAux_spec d (d + 2) 0 (d + 1) (by simp) (by nlinarith) (by omega) (by omega)

-- An integer whose square is at most `d` is at most `isqrt d`.
theorem le_isqrt_of_sq_le {d : ℕ} {k : ℤ} (hk : k * k ≤ d) : k ≤ isqrt d := by
  obtain ⟨h1, h2⟩ := isqrt_spec d
  rcases le_or_gt k (isqrt d) with h | h
  · exact h
  exfalso
  have h3 : ((isqrt d : ℕ) : ℤ) + 1 ≤ k := by omega
  have h4 : (0 : ℤ) ≤ (isqrt d : ℕ) + 1 := by positivity
  have h5 : (((isqrt d : ℕ) : ℤ) + 1) * ((isqrt d : ℕ) + 1) ≤ k * k :=
    mul_le_mul h3 h3 h4 (by linarith)
  have h6 : ((d : ℕ) : ℤ) < (((isqrt d : ℕ) : ℤ) + 1) * ((isqrt d : ℕ) + 1) := by exact_mod_cast h2
  linarith

-- A solution of `A s² − B s + C ≤ 0` with `A > 0` is at most `⌊(B + √(B² − 4AC)) / 2A⌋`.
theorem le_root {A B C s : ℤ} (hA : 0 < A) (hQ : A * s * s - B * s + C ≤ 0) :
    ¬ (B * B - 4 * A * C < 0) ∧ s ≤ (B + isqrt (B * B - 4 * A * C).toNat) / (2 * A) := by
  have hsq : (2 * A * s - B) * (2 * A * s - B) ≤ B * B - 4 * A * C := by nlinarith
  have hD : 0 ≤ B * B - 4 * A * C := le_trans (mul_self_nonneg _) hsq
  refine ⟨by omega, ?_⟩
  rw [Int.le_ediv_iff_mul_le (by positivity)]
  have hk : 2 * A * s - B ≤ isqrt (B * B - 4 * A * C).toNat := by
    apply le_isqrt_of_sq_le
    rw [Int.toNat_of_nonneg hD]
    exact hsq
  linarith

-- Hence `s ≤ capP` whenever the quadratic inequality holds.
theorem le_capP {n T t : ℕ} {s : ℤ} (hs : 0 ≤ s)
    (hm : (0 : ℤ) < (n : ℤ) - 1 - 2 * t)
    (hQ : (4 * (((n : ℤ) - 1 - 2 * t) + t)) * s * s
      - (2 * t * (8 * t + 13 * ((n : ℤ) - 1 - 2 * t) + ((n : ℤ) - 1 - 2 * t) * ((n : ℤ) - 1 - 2 * t))) * s
      + (16 * (t : ℤ) ^ 3 + 30 * (t : ℤ) ^ 2 * ((n : ℤ) - 1 - 2 * t)
        + 4 * (t : ℤ) ^ 2 * ((n : ℤ) - 1 - 2 * t) ^ 2 + t * ((n : ℤ) - 1 - 2 * t) ^ 2
        - t * ((n : ℤ) - 1 - 2 * t) ^ 3 + 6 * T * t * ((n : ℤ) - 1 - 2 * t)) ≤ 0) :
    s ≤ capP n T t := by
  have hA : (0 : ℤ) < 4 * (((n : ℤ) - 1 - 2 * t) + t) := by
    have : (0 : ℤ) ≤ t := by positivity
    linarith
  obtain ⟨hD, hle⟩ := le_root hA hQ
  unfold capP
  simp only
  rw [if_neg hD]
  exact le_trans hle (Int.self_le_toNat _)




variable {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]

-- The non-neighbours of `x` other than `x`.
def nonNbr (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (x : Fin m) : Finset (Fin m) :=
  (G.neighborFinset x)ᶜ.erase x

theorem mem_nonNbr {x y : Fin m} : y ∈ nonNbr G x ↔ y ≠ x ∧ ¬ G.Adj x y := by
  simp [nonNbr]

theorem card_nonNbr (hG : G.LocallyLinear) (x : Fin m) :
    #(nonNbr G x) + 2 * #(trianglesAt G x) + 1 = m := by
  have h1 : #((G.neighborFinset x)ᶜ) = m - #(G.neighborFinset x) := by
    rw [Finset.card_compl, Fintype.card_fin]
  have h2 : x ∈ (G.neighborFinset x)ᶜ := by simp
  have h3 := Finset.card_erase_of_mem h2
  have h4 : #(G.neighborFinset x) = G.degree x := rfl
  have h5 := degree_eq G hG x
  have h6 : #(G.neighborFinset x) ≤ m := by
    simpa using Finset.card_le_univ (G.neighborFinset x)
  have h7 : 0 < #((G.neighborFinset x)ᶜ) := Finset.card_pos.mpr ⟨x, h2⟩
  unfold nonNbr
  omega

-- A non-adjacent pair shares at most `t_y` neighbours: each triangle at `y` holds at most one.
theorem card_inter_le_of_not_adj (hG : G.LocallyLinear) {x y : Fin m} (hxy : x ≠ y) : #(G.neighborFinset x ∩ G.neighborFinset y) ≤ #(trianglesAt G y) := by
  apply Finset.card_le_card_of_forall_subsingleton (fun u τ => u ∈ τ)
  · intro u hu
    simp only [mem_inter, mem_neighborFinset] at hu
    obtain ⟨τ, hτ, hyτ, huτ⟩ := hG.2 hu.2
    exact ⟨τ, by simp [trianglesAt, hτ, hyτ], huτ⟩
  · intro τ hτ u hu u' hu'
    simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff] at hτ
    simp only [mem_inter, mem_neighborFinset] at hu hu'
    by_contra hne
    have huu' : G.Adj u u' := hτ.1.1 hu.2 hu'.2 hne
    -- `{x, u, u'}` and `{y, u, u'}` are triangles on the edge `uu'`
    have hx : G.IsNClique 3 {x, u, u'} := is3Clique_triple_iff.mpr ⟨hu.1.1, hu'.1.1, huu'⟩
    have hy : G.IsNClique 3 {y, u, u'} := is3Clique_triple_iff.mpr ⟨hu.1.2, hu'.1.2, huu'⟩
    have hneq : ({x, u, u'} : Finset (Fin m)) ≠ {y, u, u'} := by
      intro h
      have : x ∈ ({y, u, u'} : Finset (Fin m)) := by rw [← h]; simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h1 | h1 | h1
      · exact hxy h1
      · exact G.ne_of_adj hu.1.1 h1
      · exact G.ne_of_adj hu'.1.1 h1
    have hsub := hG.1 (by simpa [mem_cliqueSet_iff] using hx)
      (by simpa [mem_cliqueSet_iff] using hy) hneq
    exact hne (hsub ⟨by simp, by simp⟩ ⟨by simp, by simp⟩)

-- Adjacent vertices share exactly one neighbour.
theorem card_inter_eq_one (hG : G.LocallyLinear) {x z : Fin m} (hxz : G.Adj x z) :
    #(G.neighborFinset x ∩ G.neighborFinset z) = 1 := by
  have h1 := card_inter_neighborFinset_le hG.edgeDisjointTriangles hxz
  have h2 : 0 < #(G.neighborFinset x ∩ G.neighborFinset z) := by
    obtain ⟨τ, hτ, hxτ, hzτ⟩ := hG.2 hxz
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hτ
    apply Finset.card_pos.mpr
    -- the third vertex of the triangle is a common neighbour
    simp only [mem_insert, mem_singleton] at hxτ hzτ
    rcases hxτ with rfl | rfl | rfl <;> rcases hzτ with rfl | rfl | rfl
    all_goals first
      | exact absurd hxz (G.loopless _)
      | exact ⟨c, by simp [hac, hbc]⟩
      | exact ⟨b, by simp [hab, hbc.symm]⟩
      | exact ⟨a, by simp [hab.symm, hac.symm]⟩
  omega

-- A neighbour `z` of `x` has exactly `2 t_z − 2` neighbours among the non-neighbours of `x`.
theorem card_nbr_inter_nonNbr (hG : G.LocallyLinear) {x z : Fin m} (hxz : G.Adj x z) :
    #(G.neighborFinset z ∩ nonNbr G x) + 2 = 2 * #(trianglesAt G z) := by
  have hsplit : #(G.neighborFinset z ∩ nonNbr G x) + #(G.neighborFinset z \ nonNbr G x)
      = #(G.neighborFinset z) := Finset.card_inter_add_card_sdiff _ _
  have hset : G.neighborFinset z \ nonNbr G x = insert x (G.neighborFinset x ∩ G.neighborFinset z) := by
    ext u
    simp only [mem_sdiff, mem_nonNbr, mem_insert, mem_inter, mem_neighborFinset, not_and, not_not]
    constructor
    · rintro ⟨hzu, h⟩
      by_cases hux : u = x
      · exact Or.inl hux
      · exact Or.inr ⟨h hux, hzu⟩
    · rintro (rfl | ⟨hxu, hzu⟩)
      · exact ⟨hxz.symm, fun h => absurd rfl h⟩
      · exact ⟨hzu, fun _ => hxu⟩
  have hx : x ∉ G.neighborFinset x ∩ G.neighborFinset z := by simp
  rw [hset, Finset.card_insert_of_notMem hx, card_inter_eq_one hG hxz] at hsplit
  have hd : #(G.neighborFinset z) = G.degree z := rfl
  rw [hd, degree_eq G hG z] at hsplit
  omega


-- The common non-neighbourhood of `x` and `y`.
def farSet (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (x y : Fin m) : Finset (Fin m) :=
  nonNbr G x ∩ nonNbr G y

theorem mem_farSet {x y w : Fin m} :
    w ∈ farSet G x y ↔ (w ≠ x ∧ ¬ G.Adj x w) ∧ (w ≠ y ∧ ¬ G.Adj y w) := by
  simp [farSet, mem_nonNbr]

-- `|Y| = n − 2 − 2t_x − 2t_y + c` for a non-adjacent pair, by inclusion-exclusion.
theorem card_farSet (hG : G.LocallyLinear) {x y : Fin m} (hxy : x ≠ y) (hn : ¬ G.Adj x y) :
    #(farSet G x y) + 2 * #(trianglesAt G x) + 2 * #(trianglesAt G y) + 2
      = m + #(G.neighborFinset x ∩ G.neighborFinset y) := by
  have hF : farSet G x y
      = (insert x (G.neighborFinset x) ∪ insert y (G.neighborFinset y))ᶜ := by
    ext w
    simp only [mem_farSet, mem_compl, mem_union, mem_insert, mem_neighborFinset]
    tauto
  have hI : insert x (G.neighborFinset x) ∩ insert y (G.neighborFinset y)
      = G.neighborFinset x ∩ G.neighborFinset y := by
    ext w
    simp only [mem_inter, mem_insert, mem_neighborFinset]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.symm.trans h2) hxy
      · exact absurd (h1 ▸ h2) (fun h => hn h.symm)
      · exact absurd (h2 ▸ h1) hn
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, Or.inr h2⟩
  have h1 := Finset.card_union_add_card_inter (insert x (G.neighborFinset x))
    (insert y (G.neighborFinset y))
  rw [hI] at h1
  have hcx : #(insert x (G.neighborFinset x)) = 2 * #(trianglesAt G x) + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), ← degree_eq G hG x]; rfl
  have hcy : #(insert y (G.neighborFinset y)) = 2 * #(trianglesAt G y) + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), ← degree_eq G hG y]; rfl
  have h2 : #(farSet G x y)
      + #(insert x (G.neighborFinset x) ∪ insert y (G.neighborFinset y)) = m := by
    rw [hF, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ (insert x (G.neighborFinset x) ∪ insert y (G.neighborFinset y))
    rw [Fintype.card_fin] at this
    omega
  omega

-- A common neighbour `z` of a non-adjacent pair has at least `2 t_z − 4` neighbours in `Y`:
-- the neighbours of `z` outside `Y` are `x`, `y` and the two triangle partners.
theorem two_mul_le_card_inter_far_add (hG : G.LocallyLinear) {x y z : Fin m}
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    2 * #(trianglesAt G z) ≤ #(G.neighborFinset z ∩ farSet G x y) + 4 := by
  have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset z) (farSet G x y)
  have hsub : G.neighborFinset z \ farSet G x y
      ⊆ insert x (G.neighborFinset x ∩ G.neighborFinset z)
        ∪ insert y (G.neighborFinset y ∩ G.neighborFinset z) := by
    intro u hu
    simp only [mem_sdiff, mem_farSet, mem_neighborFinset] at hu
    simp only [mem_union, mem_insert, mem_inter, mem_neighborFinset]
    tauto
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (insert x (G.neighborFinset x ∩ G.neighborFinset z))
    (insert y (G.neighborFinset y ∩ G.neighborFinset z))
  have hix := Finset.card_insert_le x (G.neighborFinset x ∩ G.neighborFinset z)
  have hiy := Finset.card_insert_le y (G.neighborFinset y ∩ G.neighborFinset z)
  have h1 := card_inter_eq_one hG hxz
  have h2 := card_inter_eq_one hG hyz
  have hd : #(G.neighborFinset z) = 2 * #(trianglesAt G z) := degree_eq G hG z
  omega

-- Two common neighbours `z ≠ z'` of a non-adjacent pair share at most `t_z − 2` neighbours in
-- `Y`: they share at most `t_z` neighbours in all, among them `x` and `y`.
theorem card_inter_inter_far_add_two_le (hG : G.LocallyLinear) {x y z z' : Fin m} (hxy : x ≠ y)
    (hzz' : z ≠ z') (hxz : G.Adj x z) (hyz : G.Adj y z) (hxz' : G.Adj x z') (hyz' : G.Adj y z') :
    #(G.neighborFinset z ∩ G.neighborFinset z' ∩ farSet G x y) + 2 ≤ #(trianglesAt G z) := by
  have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset z ∩ G.neighborFinset z')
    (farSet G x y)
  have hsub : ({x, y} : Finset (Fin m))
      ⊆ (G.neighborFinset z ∩ G.neighborFinset z') \ farSet G x y := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    simp only [mem_sdiff, mem_inter, mem_neighborFinset, mem_farSet]
    rcases hu with rfl | rfl
    · exact ⟨⟨hxz.symm, hxz'.symm⟩, fun h => h.1.1 rfl⟩
    · exact ⟨⟨hyz.symm, hyz'.symm⟩, fun h => h.2.1 rfl⟩
  have h2 : #({x, y} : Finset (Fin m)) = 2 := Finset.card_pair hxy
  have h3 := Finset.card_le_card hsub
  have h4 : #(G.neighborFinset z ∩ G.neighborFinset z') ≤ #(trianglesAt G z) := by
    rw [Finset.inter_comm]
    exact card_inter_le_of_not_adj hG hzz'.symm
  omega

-- Double counting adjacencies between `F` and `Z`.
theorem sum_card_inter_eq (Z F : Finset (Fin m)) :
    ∑ w ∈ F, #(G.neighborFinset w ∩ Z) = ∑ z ∈ Z, #(G.neighborFinset z ∩ F) := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := F) (t := Z)
    (r := fun w z => G.Adj w z)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at h
  convert h using 2 with w hw z hz
  · congr 1
    ext z
    simp [mem_inter, mem_neighborFinset, mem_filter, and_comm]
  · congr 1
    ext w
    simp [mem_inter, mem_neighborFinset, mem_filter, adj_comm, and_comm]

-- Double counting pairs of adjacencies: `Σ_w a_w² = Σ_{z, z'} |N(z) ∩ N(z') ∩ F|`.
theorem sum_sq_card_inter_eq (Z F : Finset (Fin m)) :
    ∑ w ∈ F, #(G.neighborFinset w ∩ Z) ^ 2
      = ∑ z ∈ Z, ∑ z' ∈ Z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F) := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := F) (t := Z ×ˢ Z)
    (r := fun w p => G.Adj w p.1 ∧ G.Adj w p.2)
  rw [Finset.sum_product] at h
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at h
  convert h using 2 with w hw z hz
  · rw [sq, ← Finset.card_product]
    congr 1
    ext p
    simp only [mem_product, mem_inter, mem_neighborFinset, mem_filter]
    tauto
  · refine Finset.sum_congr rfl (fun z' _ => ?_)
    congr 1
    ext w
    simp only [mem_inter, mem_neighborFinset, mem_filter, adj_comm]
    tauto

-- The pair inequality: `2 Σ_{z ∈ Z} |N(z) ∩ Y| ≤ |Y| (|Z| + 1)` for a non-adjacent pair.
theorem pair_ineq (hG : G.LocallyLinear) {x y : Fin m} (hxy : x ≠ y) (hn : ¬ G.Adj x y) :
    2 * ∑ z ∈ G.neighborFinset x ∩ G.neighborFinset y, #(G.neighborFinset z ∩ farSet G x y)
      ≤ #(farSet G x y) * (#(G.neighborFinset x ∩ G.neighborFinset y) + 1) := by
  set Z := G.neighborFinset x ∩ G.neighborFinset y with hZ
  set F := farSet G x y with hF
  set ρ := ∑ z ∈ Z, #(G.neighborFinset z ∩ F) with hρ
  have hsum1 : ∑ w ∈ F, #(G.neighborFinset w ∩ Z) = ρ := sum_card_inter_eq Z F
  have hsum2 := sum_sq_card_inter_eq (G := G) Z F
  -- off-diagonal terms are at most half the diagonal ones
  have hoff : ∀ z ∈ Z, 2 * ∑ z' ∈ Z.erase z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F)
      ≤ (#Z - 1) * #(G.neighborFinset z ∩ F) := by
    intro z hz
    have hz' := hz
    simp only [hZ, mem_inter, mem_neighborFinset] at hz'
    have hterm : ∀ z' ∈ Z.erase z,
        2 * #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F) ≤ #(G.neighborFinset z ∩ F) := by
      intro z' hz''
      simp only [mem_erase, hZ, mem_inter, mem_neighborFinset] at hz''
      have h1 := card_inter_inter_far_add_two_le hG hxy (Ne.symm hz''.1) hz'.1 hz'.2 hz''.2.1 hz''.2.2
      have h2 := two_mul_le_card_inter_far_add hG (y := y) hz'.1 hz'.2
      rw [← hF] at h1 h2
      omega
    calc 2 * ∑ z' ∈ Z.erase z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F)
        = ∑ z' ∈ Z.erase z, 2 * #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _z' ∈ Z.erase z, #(G.neighborFinset z ∩ F) := Finset.sum_le_sum hterm
      _ = (#Z - 1) * #(G.neighborFinset z ∩ F) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hz]
  have hdiag : ∀ z ∈ Z, ∑ z' ∈ Z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F)
      = #(G.neighborFinset z ∩ F)
        + ∑ z' ∈ Z.erase z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F) := by
    intro z hz
    rw [← Finset.add_sum_erase Z _ hz, Finset.inter_self]
  have h2 : 2 * ∑ w ∈ F, #(G.neighborFinset w ∩ Z) ^ 2 ≤ (#Z + 1) * ρ := by
    rw [hsum2, Finset.mul_sum]
    calc ∑ z ∈ Z, 2 * ∑ z' ∈ Z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F)
        = ∑ z ∈ Z, (2 * #(G.neighborFinset z ∩ F)
            + 2 * ∑ z' ∈ Z.erase z, #(G.neighborFinset z ∩ G.neighborFinset z' ∩ F)) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [hdiag z hz]; ring
      _ ≤ ∑ z ∈ Z, (2 * #(G.neighborFinset z ∩ F) + (#Z - 1) * #(G.neighborFinset z ∩ F)) :=
          Finset.sum_le_sum (fun z hz => by have := hoff z hz; omega)
      _ = (#Z + 1) * ρ := by
          rw [hρ, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z hz => ?_)
          have hpos : 1 ≤ #Z := Finset.card_pos.mpr ⟨z, hz⟩
          have : 2 + (#Z - 1) = #Z + 1 := by omega
          rw [← add_mul, this]
  have hcs := sq_sum_le_card_mul_sum_sq (s := F) (f := fun w => #(G.neighborFinset w ∩ Z))
  rw [hsum1] at hcs
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have : 2 * ρ * ρ ≤ #F * (#Z + 1) * ρ := by nlinarith
    exact Nat.le_of_mul_le_mul_right this hpos


-- Double counting over the non-neighbours `y` of `x` and the common neighbours `z` of `x, y`.
theorem sum_sum_common_eq (x : Fin m) (f : Fin m → ℤ) :
    ∑ y ∈ nonNbr G x, ∑ z ∈ G.neighborFinset x ∩ G.neighborFinset y, f z
      = ∑ z ∈ G.neighborFinset x, (#(G.neighborFinset z ∩ nonNbr G x) : ℤ) * f z := by
  rw [Finset.sum_comm' (t' := G.neighborFinset x)
    (s' := fun z => G.neighborFinset z ∩ nonNbr G x)
    (f := fun (_ : Fin m) (z : Fin m) => f z)
    (fun y z => by
      simp only [mem_inter, mem_neighborFinset, adj_comm]
      tauto)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

-- The vertex set splits into `x`, its neighbours and its non-neighbours.
theorem sum_split (x : Fin m) (f : Fin m → ℕ) :
    ∑ v, f v = f x + ∑ u ∈ G.neighborFinset x, f u + ∑ y ∈ nonNbr G x, f y := by
  have h1 : (Finset.univ : Finset (Fin m)) = insert x (G.neighborFinset x) ∪ nonNbr G x := by
    ext v
    simp only [mem_univ, mem_union, mem_insert, mem_neighborFinset, mem_nonNbr, true_iff]
    tauto
  have hd : Disjoint (insert x (G.neighborFinset x)) (nonNbr G x) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [mem_insert, mem_neighborFinset] at hv
    simp only [mem_nonNbr] at hv'
    tauto
  rw [h1, Finset.sum_union hd, Finset.sum_insert (by simp)]

-- The closing algebra: the three inequalities add up exactly to the quadratic inequality.
theorem final_algebra {t s T w Z2 C2 E : ℤ}
    (hstar : 8 * Z2 - 24 * s + 32 * t + C2 ≤ w * E + w * (w - 1) - 6 * T + 2 * t + 2 * s)
    (hA8 : s ^ 2 ≤ 2 * t * Z2) (hA7 : E ^ 2 ≤ w * C2) (hE : E = 2 * s - 4 * t)
    (ht : 0 ≤ t) (hw : 0 ≤ w) :
    (4 * (w + t)) * s * s - (2 * t * (8 * t + 13 * w + w * w)) * s
      + (16 * t ^ 3 + 30 * t ^ 2 * w + 4 * t ^ 2 * w ^ 2 + t * w ^ 2 - t * w ^ 3 + 6 * T * t * w)
      ≤ 0 := by
  subst hE
  have hP1 := mul_le_mul_of_nonneg_left hstar (mul_nonneg ht hw)
  have hP2 := mul_le_mul_of_nonneg_left hA8 (by positivity : (0 : ℤ) ≤ 4 * w)
  have hP3 := mul_le_mul_of_nonneg_left hA7 ht
  linear_combination hP1 + hP2 + hP3

-- The averaged pair inequality at a vertex `x` with `t ≥ 1` triangles and `w ≥ 1` non-neighbours,
-- as the quadratic inequality `A s² − B s + C ≤ 0` in `s = Σ_{u ∈ N(x)} t_u`.
theorem vertex_quadratic (hG : G.LocallyLinear) (x : Fin m) (ht : 1 ≤ #(trianglesAt G x))
    (hw : 2 * #(trianglesAt G x) + 1 < m) :
    (4 * (((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ)) + (#(trianglesAt G x) : ℤ)))
        * (∑ u ∈ G.neighborFinset x, (#(trianglesAt G u) : ℤ))
        * (∑ u ∈ G.neighborFinset x, (#(trianglesAt G u) : ℤ))
      - (2 * (#(trianglesAt G x) : ℤ) * (8 * (#(trianglesAt G x) : ℤ)
          + 13 * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ))
          + ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ)) * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ))))
        * (∑ u ∈ G.neighborFinset x, (#(trianglesAt G u) : ℤ))
      + (16 * (#(trianglesAt G x) : ℤ) ^ 3
          + 30 * (#(trianglesAt G x) : ℤ) ^ 2 * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ))
          + 4 * (#(trianglesAt G x) : ℤ) ^ 2 * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ)) ^ 2
          + (#(trianglesAt G x) : ℤ) * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ)) ^ 2
          - (#(trianglesAt G x) : ℤ) * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ)) ^ 3
          + 6 * (#(G.cliqueFinset 3) : ℤ) * (#(trianglesAt G x) : ℤ)
            * ((m : ℤ) - 1 - 2 * (#(trianglesAt G x) : ℤ))) ≤ 0 := by
  set W := nonNbr G x with hWdef
  set N := G.neighborFinset x with hNdef
  set t : ℕ := #(trianglesAt G x) with htdef
  set tf : Fin m → ℕ := fun v => #(trianglesAt G v) with htf
  set s : ℕ := ∑ u ∈ N, tf u with hsdef
  set T : ℕ := #(G.cliqueFinset 3) with hTdef
  set c : Fin m → ℕ := fun y => #(N ∩ G.neighborFinset y) with hc
  set F : Fin m → Finset (Fin m) := fun y => farSet G x y with hFdef
  set ρ : Fin m → ℕ := fun y => ∑ z ∈ N ∩ G.neighborFinset y, #(G.neighborFinset z ∩ F y) with hρ
  have hWc : #W + 2 * t + 1 = m := card_nonNbr hG x
  have hNc : #N = 2 * t := degree_eq G hG x
  have hmemW : ∀ y ∈ W, y ≠ x ∧ ¬ G.Adj x y := fun y hy => mem_nonNbr.mp hy
  -- (2) the pair inequality at every non-neighbour
  have hpair : ∀ y ∈ W, 2 * ρ y ≤ #(F y) * (c y + 1) := fun y hy =>
    pair_ineq hG (hmemW y hy).1.symm (hmemW y hy).2
  -- (3) the size of the common non-neighbourhood
  have hfar : ∀ y ∈ W, #(F y) + 2 * t + 2 * tf y + 2 = m + c y := fun y hy =>
    card_farSet hG (hmemW y hy).1.symm (hmemW y hy).2
  -- (4) common neighbours have many neighbours in the common non-neighbourhood
  have hρge : ∀ y ∈ W, ∑ z ∈ N ∩ G.neighborFinset y, (2 * (tf z : ℤ) - 4) ≤ (ρ y : ℤ) := by
    intro y hy
    simp only [hρ, hFdef]
    push_cast
    refine Finset.sum_le_sum (fun z hz => ?_)
    simp only [hNdef, mem_inter, mem_neighborFinset] at hz
    have := two_mul_le_card_inter_far_add hG (y := y) hz.1 hz.2
    simp only [htf]
    omega
  -- (6) neighbours of `x` have `2 t_z − 2` neighbours among the non-neighbours of `x`
  have hnb : ∀ z ∈ N, (#(G.neighborFinset z ∩ W) : ℤ) = 2 * (tf z : ℤ) - 2 := by
    intro z hz
    simp only [hNdef, mem_neighborFinset] at hz
    have := card_nbr_inter_nonNbr hG hz
    rw [← hWdef] at this
    simp only [htf]
    omega
  -- (7) `c_y ≤ t_y`
  have hcle : ∀ y ∈ W, c y ≤ tf y := fun y hy =>
    card_inter_le_of_not_adj hG (hmemW y hy).1.symm
  -- (8) the triangle counts add up to `3T`
  have hsplit := sum_split (G := G) x tf
  have h3T : ∑ v, tf v = 3 * T := SqueezeBench.RuzsaSzemeredi.Upper.V006.sum_card_trianglesAt G
  -- (5)+(6): the summed lower bound on `Σ ρ_y`
  have hA2 : ∑ z ∈ N, (2 * (tf z : ℤ) - 4) * (2 * (tf z : ℤ) - 2) ≤ ∑ y ∈ W, (ρ y : ℤ) := by
    calc ∑ z ∈ N, (2 * (tf z : ℤ) - 4) * (2 * (tf z : ℤ) - 2)
        = ∑ z ∈ N, (#(G.neighborFinset z ∩ W) : ℤ) * (2 * (tf z : ℤ) - 4) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [hnb z hz]; ring
      _ = ∑ y ∈ W, ∑ z ∈ N ∩ G.neighborFinset y, (2 * (tf z : ℤ) - 4) :=
          (sum_sum_common_eq x (fun z => 2 * (tf z : ℤ) - 4)).symm
      _ ≤ ∑ y ∈ W, (ρ y : ℤ) := Finset.sum_le_sum hρge
  -- (5) with `f = 1`: `Σ c_y = 2s − 4t`
  have hE : ∑ y ∈ W, (c y : ℤ) = 2 * (s : ℤ) - 4 * t := by
    calc ∑ y ∈ W, (c y : ℤ)
        = ∑ y ∈ W, ∑ z ∈ N ∩ G.neighborFinset y, (1 : ℤ) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          simp [hc]
      _ = ∑ z ∈ N, (#(G.neighborFinset z ∩ W) : ℤ) * 1 := sum_sum_common_eq x (fun _ => 1)
      _ = ∑ z ∈ N, (2 * (tf z : ℤ) - 2) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [hnb z hz, mul_one]
      _ = 2 * (s : ℤ) - 4 * t := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hNc, hsdef]
          push_cast
          ring
  -- (8): `Σ_W t_y = 3T − t − s`
  have hTW : ∑ y ∈ W, (tf y : ℤ) = 3 * (T : ℤ) - t - s := by
    have : (∑ v, (tf v : ℤ)) = (tf x : ℤ) + ∑ u ∈ N, (tf u : ℤ) + ∑ y ∈ W, (tf y : ℤ) := by
      exact_mod_cast hsplit
    have h3T' : (∑ v, (tf v : ℤ)) = 3 * (T : ℤ) := by exact_mod_cast h3T
    have hx : (tf x : ℤ) = t := rfl
    have hs' : (∑ u ∈ N, (tf u : ℤ)) = (s : ℤ) := by simp [hsdef]
    linarith
  -- the summed right-hand sides
  have hA1 : 2 * ∑ y ∈ W, (ρ y : ℤ) ≤ ∑ y ∈ W, (#(F y) : ℤ) * (c y + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun y hy => ?_)
    exact_mod_cast hpair y hy
  have hA3 : ∑ y ∈ W, (#(F y) : ℤ) * (c y + 1)
      = ∑ y ∈ W, ((c y : ℤ) ^ 2 + ((#W : ℤ) - 2 * tf y) * c y + ((#W : ℤ) - 1) - 2 * tf y) := by
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 := hfar y hy
    have h2 : (#(F y) : ℤ) = (#W : ℤ) + c y - 2 * tf y - 1 := by
      have : (#(F y) : ℤ) + 2 * t + 2 * tf y + 2 = m + c y := by exact_mod_cast h1
      have : (#W : ℤ) + 2 * t + 1 = m := by exact_mod_cast hWc
      linarith
    rw [h2]; ring
  have hA4 : ∑ y ∈ W, (c y : ℤ) ^ 2 ≤ ∑ y ∈ W, (c y : ℤ) * tf y := by
    refine Finset.sum_le_sum (fun y hy => ?_)
    have := hcle y hy
    have h0 : (0 : ℤ) ≤ c y := by positivity
    have : (c y : ℤ) ≤ tf y := by exact_mod_cast this
    nlinarith
  -- Cauchy–Schwarz twice
  have hA7 : (∑ y ∈ W, (c y : ℤ)) ^ 2 ≤ (#W : ℤ) * ∑ y ∈ W, (c y : ℤ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := W) (f := fun y => c y)
    exact_mod_cast this
  have hA8 : (s : ℤ) ^ 2 ≤ 2 * (t : ℤ) * ∑ z ∈ N, (tf z : ℤ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := N) (f := fun z => tf z)
    rw [hNc] at this
    rw [hsdef]
    exact_mod_cast this
  -- expand the left-hand side of `hA2`
  have hA2' : ∑ z ∈ N, (2 * (tf z : ℤ) - 4) * (2 * (tf z : ℤ) - 2)
      = 4 * ∑ z ∈ N, (tf z : ℤ) ^ 2 - 12 * s + 16 * t := by
    have h1 : ∑ z ∈ N, (2 * (tf z : ℤ) - 4) * (2 * (tf z : ℤ) - 2)
        = ∑ z ∈ N, (4 * (tf z : ℤ) ^ 2 - 12 * (tf z : ℤ) + 8) := by
      refine Finset.sum_congr rfl (fun z _ => by ring)
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, hNc, hsdef]
    push_cast
    ring
  -- collect everything
  set Z2 := ∑ z ∈ N, (tf z : ℤ) ^ 2 with hZ2
  set C2 := ∑ y ∈ W, (c y : ℤ) ^ 2 with hC2
  set CT := ∑ y ∈ W, (c y : ℤ) * tf y with hCT
  set E := ∑ y ∈ W, (c y : ℤ) with hEdef
  set TW := ∑ y ∈ W, (tf y : ℤ) with hTWdef
  set w : ℤ := (#W : ℤ) with hwdef
  have hexp : ∑ y ∈ W, ((c y : ℤ) ^ 2 + (w - 2 * tf y) * c y + (w - 1) - 2 * tf y)
      = C2 + w * E - 2 * CT + #W * (w - 1) - 2 * TW := by
    have h1 : ∑ y ∈ W, (w - 2 * (tf y : ℤ)) * c y
        = w * ∑ y ∈ W, (c y : ℤ) - 2 * ∑ y ∈ W, (c y : ℤ) * tf y := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => by ring)
    simp only [hC2, hEdef, hCT, hTWdef]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, h1, ← Finset.mul_sum]
    ring
  have hstar : 8 * Z2 - 24 * (s : ℤ) + 32 * t + C2
      ≤ w * E + w * (w - 1) - 6 * T + 2 * t + 2 * s := by
    rw [hA2'] at hA2
    rw [hA3, hexp] at hA1
    have hw' : (#W : ℤ) = w := rfl
    rw [hw'] at hA1
    linarith [hA1, hA2, hA4, hTW]
  have hwm : (m : ℤ) - 1 - 2 * t = w := by
    have : (#W : ℤ) + 2 * t + 1 = m := by exact_mod_cast hWc
    linarith
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hw1 : (1 : ℤ) ≤ w := by
    have : 2 * t + 1 < m := hw
    have : (2 * (t : ℤ) + 1) < m := by exact_mod_cast this
    linarith
  have hs' : (∑ u ∈ G.neighborFinset x, (#(trianglesAt G u) : ℤ)) = (s : ℤ) := by
    simp only [hsdef, htf]
    push_cast
    rfl
  rw [hwm, hs']
  exact final_algebra hstar hA8 hA7 hE (by positivity) (by linarith)


-- Every vertex satisfies `s_v ≤ cap' t_v`: (A) and (B) from V007 give `capAB`, the averaged
-- pair inequality gives `capP`.
theorem le_cap' (hG : G.LocallyLinear) (v : Fin m) :
    ((∑ u ∈ G.neighborFinset v, #(trianglesAt G u) : ℕ) : ℤ)
      ≤ cap' m #(G.cliqueFinset 3) #(trianglesAt G v) := by
  have hA := SqueezeBench.RuzsaSzemeredi.Upper.V007.sum_nbr_le hG v
  have hB := SqueezeBench.RuzsaSzemeredi.Upper.V007.two_mul_sum_nbr_le hG v
  have hAB : ∑ u ∈ G.neighborFinset v, #(trianglesAt G u)
      ≤ capAB m #(G.cliqueFinset 3) #(trianglesAt G v) := by
    unfold capAB SqueezeBench.RuzsaSzemeredi.Upper.V007.cap
    rw [Nat.le_div_iff_mul_le (by norm_num), Nat.mul_two, le_min_iff]
    constructor
    · omega
    · have h2 : 2 * #(trianglesAt G v) * #(trianglesAt G v)
          ≤ #(trianglesAt G v) * (m + 2 + m % 2) := le_trans (Nat.le_add_left _ _) hB
      generalize #(trianglesAt G v) * (m + 2 + m % 2) = X at hB h2 ⊢
      generalize 2 * #(trianglesAt G v) * #(trianglesAt G v) = Y at hB h2 ⊢
      omega
  unfold cap'
  split
  · rename_i h
    rw [Nat.cast_min, le_min_iff]
    refine ⟨by exact_mod_cast hAB, ?_⟩
    have hq := vertex_quadratic hG v h.1 h.2
    have hm : (0 : ℤ) < (m : ℤ) - 1 - 2 * (#(trianglesAt G v) : ℤ) := by
      have : 2 * #(trianglesAt G v) + 1 < m := h.2
      have : (2 * (#(trianglesAt G v) : ℤ) + 1) < m := by exact_mod_cast this
      linarith
    push_cast
    exact le_capP (by positivity) hm hq
  · exact_mod_cast hAB

-- Hence `ψ(t_v) ≤ 4 t_v² − 2 s_v` at every vertex.
theorem psi_le (hG : G.LocallyLinear) (v : Fin m) :
    psi m #(G.cliqueFinset 3) #(trianglesAt G v)
      ≤ 4 * (#(trianglesAt G v) : ℤ) ^ 2
        - 2 * ∑ u ∈ G.neighborFinset v, (#(trianglesAt G u) : ℤ) := by
  have h := le_cap' hG v
  push_cast at h
  unfold psi
  linarith

-- Every vertex has at most `(m − 1) / 2` triangles.
theorem card_trianglesAt_le (hG : G.LocallyLinear) (v : Fin m) :
    #(trianglesAt G v) ≤ (m - 1) / 2 := by
  have h1 : G.degree v ≤ m - 1 := by
    have := G.degree_lt_card_verts v
    rw [Fintype.card_fin] at this
    omega
  have h2 := degree_eq G hG v
  omega

-- If the chord test reports nothing, the chord lies below `ψ` on the whole range.
theorem lineAbove_false {n T q : ℕ} {a b : ℤ} :
    ∀ bound, lineAbove n T q a b bound = false →
      ∀ t, t ≤ bound → a + (b - a) * ((t : ℤ) - q) ≤ psi n T t := by
  intro bound
  induction bound with
  | zero =>
    intro h t ht
    have ht0 : t = 0 := by omega
    subst ht0
    simp only [lineAbove, decide_eq_false_iff_not, not_lt] at h
    simpa using h
  | succ k ih =>
    intro h t ht
    simp only [lineAbove, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h
    rcases Nat.lt_or_ge t (k + 1) with hlt | hge
    · exact ih h.2 t (by omega)
    · have : t = k + 1 := by omega
      subst this
      exact h.1

-- The chord through the balanced points sums to the balanced value.
theorem sum_chord {n : ℕ} (t : Fin n → ℕ) (q r : ℕ) (a b : ℤ) (hS : ∑ v, t v = q * n + r) :
    ∑ v, (a + (b - a) * ((t v : ℤ) - q)) = ((n : ℤ) - r) * a + r * b := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hS' : (∑ v, (t v : ℤ)) = q * n + r := by exact_mod_cast hS
  rw [hS']
  simp only [nsmul_eq_mul]
  ring

-- The triangle count of a locally linear graph passes the test.
theorem ok_of_graph {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : ok n #(G.cliqueFinset 3) = true := by
  set T := #(G.cliqueFinset 3) with hT
  set t : Fin n → ℕ := fun v => #(trianglesAt G v) with ht
  by_contra hfalse
  have h : ok n T = false := by simpa using hfalse
  simp only [ok, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le] at h
  obtain ⟨hpos, hline⟩ := h
  set q := 3 * T / n with hq
  set r := 3 * T % n with hr
  have hS : ∑ v, t v = q * n + r := by
    have h1 : ∑ v, t v = 3 * T := SqueezeBench.RuzsaSzemeredi.Upper.V006.sum_card_trianglesAt G
    have h2 := Nat.div_add_mod (3 * T) n
    rw [h1, ← h2]; ring
  have hchord := lineAbove_false _ hline
  -- the chord is below `ψ` at every vertex, and `ψ` is below `4t² − 2s`
  have hvert : ∀ v, psi n T q + (psi n T (q + 1) - psi n T q) * ((t v : ℤ) - q)
      ≤ 4 * (t v : ℤ) ^ 2 - 2 * ∑ u ∈ G.neighborFinset v, (t u : ℤ) := fun v =>
    le_trans (hchord (t v) (card_trianglesAt_le hG v)) (psi_le hG v)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hvert v)
  rw [sum_chord t q r _ _ hS] at hsum
  -- but `Σ (4 t_v² − 2 s_v) = 0`
  have hzero : ∑ v, (4 * (t v : ℤ) ^ 2 - 2 * ∑ u ∈ G.neighborFinset v, (t u : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := SqueezeBench.RuzsaSzemeredi.Upper.V007.sum_sum_nbr_eq hG
    have hc : ((∑ v : Fin n, ∑ u ∈ G.neighborFinset v, #(trianglesAt G u) : ℕ) : ℤ)
        = ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, (t u : ℤ) := by push_cast; rfl
    have hc2 : ((2 * ∑ v : Fin n, #(trianglesAt G v) ^ 2 : ℕ) : ℤ)
        = 2 * ∑ v : Fin n, (t v : ℤ) ^ 2 := by push_cast; rfl
    have h3 : ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, (t u : ℤ)
        = 2 * ∑ v : Fin n, (t v : ℤ) ^ 2 := by rw [← hc, ← hc2, this]
    rw [h3]; ring
  rw [hzero] at hsum
  linarith

theorem search_le (n : ℕ) : ∀ T, search n T ≤ T := by
  intro T
  induction T with
  | zero => simp [search]
  | succ T ih =>
    simp only [search]
    cases ok n (T + 1)
    · simp; omega
    · simp

theorem le_search (n : ℕ) {T : ℕ} (hT : ok n T = true) : ∀ T₀, T ≤ T₀ → T ≤ search n T₀ := by
  intro T₀
  induction T₀ with
  | zero => intro h; omega
  | succ T₀ ih =>
    intro h
    simp only [search]
    rcases Nat.lt_or_ge T (T₀ + 1) with hlt | hge
    · have := ih (by omega)
      cases hok : ok n (T₀ + 1)
      · simpa using this
      · simp; omega
    · have hEq : T = T₀ + 1 := by omega
      subst hEq
      rw [hT]; rfl

theorem ok_ruzsaSzemeredi {n : ℕ} (hn : 0 < n) : ok n (ruzsaSzemerediNumberNat n) = true := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  exact ok_of_graph hn hLL

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · have hprev := SqueezeBench.RuzsaSzemeredi.Upper.V007.valid n
    rw [SqueezeBench.RuzsaSzemeredi.f_of_le h] at hprev ⊢
    have h' : 3 ≤ n := h
    exact le_search n (ok_ruzsaSzemeredi (by omega)) _ hprev

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V007.record record :=
  fun n => search_le n _

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V007.record record :=
  ⟨40, by decide, by decide +kernel⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V008
