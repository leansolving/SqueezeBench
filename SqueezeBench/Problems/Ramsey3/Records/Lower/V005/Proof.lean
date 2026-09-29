import SqueezeBench.Problems.Ramsey3.Records.Lower.V005.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V004.Proof

-- Record V005 for Ramsey3, lower direction, by trial claude-fable.
--
-- `Good N m` says some graph on `Fin N` is triangle-free with every independent set of size
-- at most `m`; `R(3,k) > N` follows from `Good N (k-1)`. Three ways to produce it:
--
-- * the base graphs of V004 (unbalanced blow-up of `C₁₃(±1,±5)`) and V001 (of `C₅`), reusing
--   their lemmas verbatim: `Good (base m) m`;
-- * pulling back along an injection (fewer vertices, same bound): `Good N m → Good N' m` for
--   `N' ≤ N`, and transport along `Fin N × Fin 6 ≃ Fin (N * 6)`;
-- * the Chung–Cleve–Dagum fibration `fib G` on `V × Fin 6`: `(u,i) ~ (v,j)` iff `u ~ v` and
--   the layers `i, j` are at cyclic distance at most `1`, or `u = v` and `j = i + 3`.
--   Triangle-free: a triangle of `G`-edges projects to a triangle of `G`; a matching edge
--   `(u,i),(u,i+3)` has no common neighbour, since `j` would be within `1` of both `i` and
--   `i+3` (`omega`). Independence: an independent set `T` has layers `A_i`, with `A_i ∪ A_{i+1}`
--   independent in `G` and `A_i ∩ A_{i+3} = ∅`. Then `B = (A₀∩A₁) ∪ (A₂∩A₃) ∪ (A₄∩A₅)` is a
--   disjoint union of three sets and independent in `G`, so `Σ|A_i| = Σ_r |A_{2r} ∪ A_{2r+1}|
--   + |B| ≤ 3m + m` (the six-set lemma). So `Good N m → Good (6N) (4m)`.
--
-- `g` recurses `Good (g m) m` through these, and `v k = g (k-1) + 1`.
-- Source of the construction: F. R. K. Chung, R. Cleve, P. Dagum, A note on constructive lower
-- bounds for the Ramsey numbers R(3,t), J. Combin. Theory Ser. B 57 (1993) 150–155.

namespace SqueezeBench.Ramsey3.Lower.V005

open SqueezeBench SimpleGraph Finset

-- `G` is triangle-free and every independent set has at most `m` vertices.
def GoodOn {V : Type} (G : SimpleGraph V) (m : ℕ) : Prop :=
  G.CliqueFree 3 ∧ ∀ T : Finset V, (∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y) → T.card ≤ m

-- Some graph on `Fin N` is triangle-free with independence number at most `m`.
def Good (N m : ℕ) : Prop := ∃ G : SimpleGraph (Fin N), GoodOn G m

-- Cliques of the complement are independent sets.
theorem indep_of_isClique_compl {V : Type} {G : SimpleGraph V} {T : Finset V}
    (hT : Gᶜ.IsClique ↑T) : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y := by
  intro x hx y hy hadj
  rcases eq_or_ne x y with rfl | hne
  · exact G.ne_of_adj hadj rfl
  · exact ((compl_adj G x y).mp (hT hx hy hne)).2 hadj

-- Pulling back along an injection keeps both properties.
theorem goodOn_comap {V W : Type} {H : SimpleGraph W} {m : ℕ} (hH : GoodOn H m)
    (f : V ↪ W) : GoodOn (H.comap f) m := by
  refine ⟨?_, ?_⟩
  · intro S hS
    refine hH.1 (S.map f) ⟨?_, by rw [Finset.card_map]; exact hS.card_eq⟩
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    exact hS.isClique hx hy (fun h => hab (h ▸ rfl))
  intro T hT
  have h := hH.2 (T.map f) ?_
  · rwa [Finset.card_map] at h
  · intro x hx y hy hadj
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact hT x' hx' y' hy' hadj

theorem good_mono {N N' m : ℕ} (h : N' ≤ N) (hN : Good N m) : Good N' m := by
  obtain ⟨G, hG⟩ := hN
  exact ⟨G.comap (Fin.castLEEmb h), goodOn_comap hG _⟩

theorem good_mono_m {N m m' : ℕ} (h : m ≤ m') (hN : Good N m) : Good N m' := by
  obtain ⟨G, h1, h2⟩ := hN
  exact ⟨G, h1, fun T hT => (h2 T hT).trans h⟩

theorem good_max {a b m : ℕ} (ha : Good a m) (hb : Good b m) : Good (max a b) m := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

-- The base graphs, from V004 and V001.
theorem good_c13 (m : ℕ) : Good (13 * (m / 4) + 2 * (m % 4)) m := by
  refine ⟨SqueezeBench.Ramsey3.Lower.V003.cg _,
    SqueezeBench.Ramsey3.Lower.V003.cg_cliqueFree_three, ?_⟩
  intro T hT
  have h := SqueezeBench.Ramsey3.Lower.V004.indep_card_le (q := m / 4) (r := m % 4) (T := T)
    (by omega) le_rfl ?_
  · omega
  · intro x hx y hy hr
    exact hT x hx y hy ((SqueezeBench.Ramsey3.Lower.V003.cg_adj x y).mpr hr)

theorem good_c5 (m : ℕ) : Good (5 * m / 2) m := by
  refine ⟨SqueezeBench.Ramsey3.Lower.V001.blowC5 _,
    SqueezeBench.Ramsey3.Lower.V001.blowC5_cliqueFree_three _, ?_⟩
  intro T hT
  refine SqueezeBench.Ramsey3.Lower.V001.indep_card_le le_rfl ?_
  intro x hx y hy hne
  rw [compl_adj]
  exact ⟨hne, hT x hx y hy⟩

theorem good_base (m : ℕ) : Good (base m) m := good_max (good_c13 m) (good_c5 m)

-- Layers of `Z₆` at cyclic distance at most one, and antipodal layers.
def near (i j : ℕ) : Prop := (i + 1) % 6 = j % 6 ∨ i % 6 = j % 6 ∨ (j + 1) % 6 = i % 6

def opp (i j : ℕ) : Prop := (i + 3) % 6 = j % 6

theorem near_symm {i j : ℕ} (h : near i j) : near j i := by unfold near at h ⊢; omega

theorem opp_symm {i j : ℕ} (h : opp i j) : opp j i := by unfold opp at h ⊢; omega

theorem opp_irrefl (i : ℕ) : ¬ opp i i := by unfold opp; omega

instance (i j : ℕ) : Decidable (near i j) := by unfold near; infer_instance

instance (i j : ℕ) : Decidable (opp i j) := by unfold opp; infer_instance

-- The fibration of `G`.
def fib {V : Type} (G : SimpleGraph V) : SimpleGraph (V × Fin 6) :=
  SimpleGraph.fromRel (fun x y =>
    (G.Adj x.1 y.1 ∧ near x.2.val y.2.val) ∨ (x.1 = y.1 ∧ opp x.2.val y.2.val))

theorem fib_adj {V : Type} (G : SimpleGraph V) (x y : V × Fin 6) :
    (fib G).Adj x y ↔
      (G.Adj x.1 y.1 ∧ near x.2.val y.2.val) ∨ (x.1 = y.1 ∧ opp x.2.val y.2.val) := by
  unfold fib
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, near_symm h2⟩
      · exact Or.inr ⟨h1.symm, opp_symm h2⟩
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact G.ne_of_adj h1 rfl
    · exact opp_irrefl _ h2

-- A triangle of the fibration is a triangle of `G`, or a matching edge with a common
-- neighbour, which the layer arithmetic forbids.
theorem fib_cliqueFree {V : Type} [DecidableEq V] {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (fib G).CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  have h1 := (fib_adj G a b).mp (hS.isClique (by simp) (by simp) hab)
  have h2 := (fib_adj G a c).mp (hS.isClique (by simp) (by simp) hac)
  have h3 := (fib_adj G b c).mp (hS.isClique (by simp) (by simp) hbc)
  rcases h1 with ⟨g1, n1⟩ | ⟨e1, o1⟩ <;> rcases h2 with ⟨g2, n2⟩ | ⟨e2, o2⟩ <;>
    rcases h3 with ⟨g3, n3⟩ | ⟨e3, o3⟩
  · exact hG _ (is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩)
  · unfold near opp at *; omega
  · unfold near opp at *; omega
  · rw [e2, e3] at g1; exact G.ne_of_adj g1 rfl
  · unfold near opp at *; omega
  · rw [e1, e3] at g2; exact G.ne_of_adj g2 rfl
  · rw [← e1, ← e2] at g3; exact G.ne_of_adj g3 rfl
  · unfold opp at o1 o2 o3; omega

-- The six-set lemma: layers with consecutive unions independent and antipodal layers disjoint
-- have total size at most `4m`.
theorem six_set {V : Type} [DecidableEq V] {G : SimpleGraph V} {m : ℕ}
    (hm : ∀ S : Finset V, (∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) → S.card ≤ m)
    (A : Fin 6 → Finset V)
    (hnear : ∀ i j : Fin 6, near i.val j.val → ∀ x ∈ A i, ∀ y ∈ A j, ¬ G.Adj x y)
    (hopp : ∀ i j : Fin 6, opp i.val j.val → Disjoint (A i) (A j)) :
    ∑ i, (A i).card ≤ 4 * m := by
  have hU : ∀ i j : Fin 6, near i.val j.val → (A i ∪ A j).card ≤ m := by
    intro i j hij
    apply hm
    intro x hx y hy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact hnear i i (by unfold near; omega) x hx y hy
    · exact hnear i j hij x hx y hy
    · exact hnear j i (near_symm hij) x hx y hy
    · exact hnear j j (by unfold near; omega) x hx y hy
  have h01 := hU 0 1 (by decide)
  have h23 := hU 2 3 (by decide)
  have h45 := hU 4 5 (by decide)
  have hB : ((A 0 ∩ A 1) ∪ (A 2 ∩ A 3) ∪ (A 4 ∩ A 5)).card ≤ m := by
    apply hm
    intro x hx y hy
    simp only [Finset.mem_union, Finset.mem_inter] at hx hy
    rcases hx with (⟨hx0, hx1⟩ | ⟨hx2, hx3⟩) | ⟨hx4, hx5⟩ <;>
      rcases hy with (⟨hy0, hy1⟩ | ⟨hy2, hy3⟩) | ⟨hy4, hy5⟩
    · exact hnear 0 0 (by decide) x hx0 y hy0
    · exact hnear 1 2 (by decide) x hx1 y hy2
    · exact hnear 0 5 (by decide) x hx0 y hy5
    · exact hnear 2 1 (by decide) x hx2 y hy1
    · exact hnear 2 2 (by decide) x hx2 y hy2
    · exact hnear 3 4 (by decide) x hx3 y hy4
    · exact hnear 5 0 (by decide) x hx5 y hy0
    · exact hnear 4 3 (by decide) x hx4 y hy3
    · exact hnear 4 4 (by decide) x hx4 y hy4
  have hd01 : Disjoint (A 0 ∩ A 1) (A 2 ∩ A 3) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (hopp 0 3 (by decide)))
  have hd2 : Disjoint ((A 0 ∩ A 1) ∪ (A 2 ∩ A 3)) (A 4 ∩ A 5) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hopp 1 4 (by decide))),
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_right (hopp 2 5 (by decide)))⟩
  rw [Finset.card_union_eq_card_add_card.mpr hd2, Finset.card_union_eq_card_add_card.mpr hd01] at hB
  have e01 := Finset.card_union_add_card_inter (A 0) (A 1)
  have e23 := Finset.card_union_add_card_inter (A 2) (A 3)
  have e45 := Finset.card_union_add_card_inter (A 4) (A 5)
  rw [Fin.sum_univ_six]
  omega

-- An independent set of the fibration has at most `4m` vertices.
theorem fib_indep_card {V : Type} [DecidableEq V] {G : SimpleGraph V} {m : ℕ}
    (hm : ∀ S : Finset V, (∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) → S.card ≤ m)
    (T : Finset (V × Fin 6)) (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ (fib G).Adj x y) :
    T.card ≤ 4 * m := by
  let A : Fin 6 → Finset V := fun i => (T.filter (fun x => x.2 = i)).image Prod.fst
  have hA : ∀ i, (T.filter (fun x => x.2 = i)).card = (A i).card := by
    intro i
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    exact Prod.ext hxy (hx.2.trans hy.2.symm)
  have hsum : T.card = ∑ i, (A i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl (fun i _ => hA i)
  rw [hsum]
  apply six_set hm A
  · intro i j hij x hx y hy hadj
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_filter] at hx' hy'
    apply hT x' hx'.1 y' hy'.1
    rw [fib_adj]
    exact Or.inl ⟨hadj, by rw [hx'.2, hy'.2]; exact hij⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hx'
    rw [Finset.mem_filter] at hy hz
    apply hT y hy.1 z hz.1
    rw [fib_adj]
    exact Or.inr ⟨hzy.symm, by rw [hy.2, hz.2]; exact hij⟩

theorem good_fib {N m : ℕ} (h : Good N m) : Good (N * 6) (4 * m) := by
  obtain ⟨G, hG3, hGi⟩ := h
  exact ⟨_, goodOn_comap ⟨fib_cliqueFree hG3, fun T hT => fib_indep_card hGi T hT⟩
    (finProdFinEquiv (m := N) (n := 6)).symm.toEmbedding⟩

theorem good_gAux (fuel : ℕ) : ∀ m, Good (gAux fuel m) m := by
  induction fuel with
  | zero => intro m; exact good_base m
  | succ f ih =>
    intro m
    simp only [gAux]
    split_ifs with hm
    · exact good_base m
    · exact good_max (good_base m)
        (good_mono_m (Nat.mul_div_le m 4) (good_fib (ih (m / 4))))

theorem good_g (m : ℕ) : Good (g m) m := good_gAux m m

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) :
    g (k - 1) + 1 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  by_contra hcon
  obtain ⟨G, hG3, hGi⟩ := good_mono (show N ≤ g (k - 1) by omega) (good_g (k - 1))
  rcases h G with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact hG3 S hS
  · have hc := hGi T (indep_of_isClique_compl hT.isClique)
    rw [hT.card_eq] at hc
    omega

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f v :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey3.Lower.V004.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V004.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V004.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 17) (by decide) (by decide)

end SqueezeBench.Ramsey3.Lower.V005
