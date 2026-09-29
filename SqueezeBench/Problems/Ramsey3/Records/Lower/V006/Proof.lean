import SqueezeBench.Problems.Ramsey3.Records.Lower.V006.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V005.Proof

-- Record V006 for Ramsey3, lower direction, by trial claude-fable.
--
-- V005's recursion with a better base. New ingredients, all in V005's language of
-- `Good N m` (a triangle-free graph on `Fin N` whose independent sets have at most `m` vertices):
--
-- * `good_union`: the disjoint sum `G ⊕g H` is good with the bounds added (a triangle lies on
--   one side; an independent set splits into its two sides), transported along
--   `finSumFinEquiv`;
-- * `good_wagner`: the Wagner graph `C₈(±1, 4)` has independence number `3` — four cyclic gaps
--   of size at least `2` summing to `8` are all `2`, which puts two antipodal vertices in;
-- * `good_k35`: the Kalbfleisch circulant `C₃₅(±1,±7,±11,±16)` has independence number `8`.
--   Write `Z₃₅ = Z₅ × Z₇`; the edges become `(a,b) ~ (a±2,b)` and `(a,b) ~ (a+1, b+d)` for
--   `d ∈ {1,2,4}`. Each layer `b` (the vertices `b + 7i`) is a 5-cycle, so it holds at most two
--   vertices of an independent set `I`, and a two-element layer is `{x, x+21}`. If at most one
--   layer holds two, `|I| ≤ 2 + 6`. Otherwise an automorphism `x ↦ q(x − x₁)` with
--   `q ∈ {1, 11, 16}` (the units fixing the connection set) moves one double to `{0, 21}` and
--   the other into layer `1`, where it must be `{8, 29}` or `{15, 29}`. Every other vertex
--   non-adjacent to those four lies in an explicit list of ten (or nine) candidates, which the
--   two 5-cycles `23,4,3,31,12` and `17,33,26,25,6` (or the 5-cycle `9,25,6,17,33` and the
--   edges `12–23`, `27–3`) cover; so at most four more vertices fit and `|I| ≤ 8`.
--   The finite facts (the candidate lists, the cycles, the layer-1 table) are checked by
--   `decide` over `Fin 5` and `Fin 35`; the modular identities are `omega`.
--
-- The base is then the knapsack `35⌊m/8⌋ + rem (m mod 8)` with `rem` from the pieces
-- `(13,4)`, `(8,3)`, `(5,2)`, `(2,1)`, and `g` is V005's recursion over it.
-- Sources: the 35-vertex graph is Kalbfleisch's (1966; Radziszowski, Small Ramsey Numbers,
-- DS1); the proof of its independence number was worked out with a literature consultation.

namespace SqueezeBench.Ramsey3.Lower.V006

open SqueezeBench SimpleGraph Finset
open SqueezeBench.Ramsey3.Lower.V005 (GoodOn Good goodOn_comap good_mono good_mono_m good_max
  good_c13 good_c5 good_fib)

-- The disjoint union of two good graphs is good, with the bounds added.
theorem goodOn_sum {V W : Type} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} {m m' : ℕ} (hG : GoodOn G m) (hH : GoodOn H m') :
    GoodOn (G ⊕g H) (m + m') := by
  refine ⟨?_, ?_⟩
  · intro S hS
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
    have h1 := hS.isClique (by simp) (by simp) hab
    have h2 := hS.isClique (by simp) (by simp) hac
    have h3 := hS.isClique (by simp) (by simp) hbc
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp only [SimpleGraph.sum_adj] at h1 h2 h3
    · exact hG.1 _ (is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
    · exact hH.1 _ (is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
  · intro T hT
    have hL : T.toLeft.card ≤ m := by
      apply hG.2
      intro x hx y hy hadj
      rw [Finset.mem_toLeft] at hx hy
      exact hT _ hx _ hy hadj
    have hR : T.toRight.card ≤ m' := by
      apply hH.2
      intro x hx y hy hadj
      rw [Finset.mem_toRight] at hx hy
      exact hT _ hx _ hy hadj
    have := Finset.card_toLeft_add_card_toRight (u := T)
    omega

theorem good_union {N N' m m' : ℕ} (h : Good N m) (h' : Good N' m') : Good (N + N') (m + m') := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨H, hH⟩ := h'
  exact ⟨_, goodOn_comap (goodOn_sum hG hH) (finSumFinEquiv (m := N) (n := N')).symm.toEmbedding⟩

-- The Wagner graph `C₈(±1, 4)`: triangle-free with independence number `3`.
def wadj (x y : ℕ) : Prop := (x + 1) % 8 = y % 8 ∨ (x + 4) % 8 = y % 8 ∨ (y + 1) % 8 = x % 8

def wg : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun x y : Fin 8 => wadj (x : ℕ) (y : ℕ))

theorem wg_adj (x y : Fin 8) : wg.Adj x y ↔ wadj (x : ℕ) (y : ℕ) := by
  unfold wg
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · unfold wadj at h ⊢; omega
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    unfold wadj at h; omega

theorem wg_cliqueFree : wg.CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  have h1 := (wg_adj a b).mp (hS.isClique (by simp) (by simp) hab)
  have h2 := (wg_adj a c).mp (hS.isClique (by simp) (by simp) hac)
  have h3 := (wg_adj b c).mp (hS.isClique (by simp) (by simp) hbc)
  unfold wadj at h1 h2 h3
  omega

-- No four vertices of the Wagner graph are pairwise non-adjacent: the four cyclic gaps are
-- at least `2` and sum to `8`, so all are `2` and two of the vertices are antipodal.
theorem wg_no_indep_four {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 8)
    (nab : ¬ wadj a b) (nbc : ¬ wadj b c) (ncd : ¬ wadj c d) (nad : ¬ wadj a d)
    (nac : ¬ wadj a c) : False := by
  have h1 : b ≠ a + 1 := fun h => nab (Or.inl (by omega))
  have h2 : c ≠ b + 1 := fun h => nbc (Or.inl (by omega))
  have h3 : d ≠ c + 1 := fun h => ncd (Or.inl (by omega))
  have h4 : d ≠ a + 7 := fun h => nad (Or.inr (Or.inr (by omega)))
  have h5 : c ≠ a + 4 := fun h => nac (Or.inr (Or.inl (by omega)))
  omega

theorem wg_indep_card_le {T : Finset (Fin 8)} (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ wg.Adj x y) :
    T.card ≤ 3 := by
  by_contra hc
  obtain ⟨S, hSR, hS⟩ := Finset.exists_subset_card_eq (show 4 ≤ T.card by omega)
  set g := S.orderIsoOfFin hS with hgdef
  have hm : ∀ i : Fin 4, (g i : Fin 8) ∈ T := fun i => hSR (g i).2
  have hlt : ∀ i j : Fin 4, i < j → ((g i : Fin 8) : ℕ) < ((g j : Fin 8) : ℕ) := by
    intro i j hij
    exact_mod_cast (g.lt_iff_lt).mpr hij
  have hn : ∀ i j : Fin 4, ¬ wadj ((g i : Fin 8) : ℕ) ((g j : Fin 8) : ℕ) :=
    fun i j h => hT _ (hm i) _ (hm j) ((wg_adj _ _).mpr h)
  exact wg_no_indep_four (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide))
    (g 3 : Fin 8).isLt (hn 0 1) (hn 1 2) (hn 2 3) (hn 0 3) (hn 0 2)

theorem good_wagner : Good 8 3 := ⟨wg, wg_cliqueFree, fun _ hT => wg_indep_card_le hT⟩

-- The Kalbfleisch circulant `C₃₅(±1, ±7, ±11, ±16)`: connection set and cyclic difference.
def S35 : Finset ℕ := {1, 7, 11, 16, 19, 24, 28, 34}

def sd (x y : ℕ) : ℕ := (y + 35 - x) % 35

def kadj (x y : ℕ) : Prop := sd x y ∈ S35 ∨ sd y x ∈ S35

instance (x y : ℕ) : Decidable (kadj x y) := by unfold kadj; infer_instance

def kg : SimpleGraph (Fin 35) := SimpleGraph.fromRel (fun x y : Fin 35 => kadj (x : ℕ) (y : ℕ))

theorem kadj_symm {x y : ℕ} (h : kadj x y) : kadj y x := by unfold kadj at h ⊢; tauto

theorem kg_adj (x y : Fin 35) : kg.Adj x y ↔ x ≠ y ∧ kadj (x : ℕ) (y : ℕ) := by
  unfold kg
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, kadj_symm h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

-- Tables about the connection set.
theorem S35_neg : ∀ s ∈ S35, (35 - s) % 35 ∈ S35 := by decide

theorem S35_sum : ∀ s ∈ S35, ∀ t ∈ S35, (s + t) % 35 ∉ S35 := by decide

theorem S35_zero : (0 : ℕ) ∉ S35 := by decide

-- Orient an adjacency.
theorem kadj_sd {x y : ℕ} (hx : x < 35) (hy : y < 35) (h : kadj x y) : sd x y ∈ S35 := by
  rcases h with h | h
  · exact h
  · have h0 : sd y x ≠ 0 := fun h0 => S35_zero (h0 ▸ h)
    have := S35_neg _ h
    have e : sd x y = (35 - sd y x) % 35 := by unfold sd at h0 ⊢; omega
    rw [e]; exact this

theorem kg_cliqueFree : kg.CliqueFree 3 := by
  intro T hT
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT.card_eq
  have h1 := ((kg_adj a b).mp (hT.isClique (by simp) (by simp) hab)).2
  have h2 := ((kg_adj a c).mp (hT.isClique (by simp) (by simp) hac)).2
  have h3 := ((kg_adj b c).mp (hT.isClique (by simp) (by simp) hbc)).2
  have s1 := kadj_sd a.isLt b.isLt h1
  have s2 := kadj_sd a.isLt c.isLt h2
  have s3 := kadj_sd b.isLt c.isLt h3
  have e : (sd a b + sd b c) % 35 = sd a c := by
    unfold sd; have := a.isLt; have := b.isLt; have := c.isLt; omega
  exact S35_sum _ s1 _ s3 (e ▸ s2)

-- A subset of `Z₅` with no two cyclically consecutive elements has at most two elements.
theorem fin5_no_consec (J : Finset (Fin 5)) (h : ∀ i ∈ J, i + 1 ∉ J) : J.card ≤ 2 := by
  revert J; decide

-- An independent set meets a 5-cycle in at most two vertices.
theorem cycle5 {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y)
    (v : Fin 5 → Fin 35) (hv : ∀ i, kg.Adj (v i) (v (i + 1))) :
    (I.filter (fun x => x ∈ Finset.univ.image v)).card ≤ 2 := by
  have hsub : I.filter (fun x => x ∈ Finset.univ.image v) ⊆
      (Finset.univ.filter (fun i : Fin 5 => v i ∈ I)).image v := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_image] at hx
    obtain ⟨hxI, i, -, rfl⟩ := hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxI⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  apply fin5_no_consec
  intro i hi hi1
  rw [Finset.mem_filter] at hi hi1
  exact hI _ hi.2 _ hi1.2 (hv i)


-- Non-adjacency inside an independent set, in the `kadj` form.
theorem indep_kadj {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y) :
    ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ kadj (x : ℕ) (y : ℕ) :=
  fun x hx y hy hne h => hI x hx y hy ((kg_adj x y).mpr ⟨hne, h⟩)

-- Layer `b`: the vertices `b + 7 i`, a 5-cycle with step `7`.
def lay (b : ℕ) (hb : b < 7) (i : Fin 5) : Fin 35 := ⟨b + 7 * (i : ℕ), by omega⟩

theorem lay_adj (b : ℕ) (hb : b < 7) (i : Fin 5) : kg.Adj (lay b hb i) (lay b hb (i + 1)) := by
  rw [kg_adj]
  have h1 : ((i + 1 : Fin 5) : ℕ) = ((i : ℕ) + 1) % 5 := by simp [Fin.val_add]
  have hi := i.isLt
  constructor
  · intro h
    have := congrArg Fin.val h
    simp only [lay, h1] at this
    omega
  · left
    have : sd (lay b hb i : ℕ) (lay b hb (i + 1) : ℕ) = 7 := by
      simp only [lay, h1, sd]; omega
    rw [this]; decide

theorem layer_card_le {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y) (b : ℕ)
    (hb : b < 7) : (I.filter (fun x : Fin 35 => (x : ℕ) % 7 = b)).card ≤ 2 := by
  have h := cycle5 hI (lay b hb) (lay_adj b hb)
  refine le_trans (Finset.card_le_card ?_) h
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, Finset.mem_image.mpr ⟨⟨(x : ℕ) / 7, by omega⟩, Finset.mem_univ _, ?_⟩⟩
  apply Fin.ext
  simp only [lay]
  omega

theorem card_eq_sum_layers (I : Finset (Fin 35)) :
    I.card = ∑ b ∈ Finset.range 7, (I.filter (fun x : Fin 35 => (x : ℕ) % 7 = b)).card :=
  Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))

-- The two normalised configurations: `0, 21 ∈ I` and a double in layer `1`.
theorem layer1_table : ∀ i j : Fin 5, i ≠ j →
    ¬ kadj (1 + 7 * (i : ℕ)) 0 → ¬ kadj (1 + 7 * (i : ℕ)) 21 →
    ¬ kadj (1 + 7 * (j : ℕ)) 0 → ¬ kadj (1 + 7 * (j : ℕ)) 21 →
    ¬ kadj (1 + 7 * (i : ℕ)) (1 + 7 * (j : ℕ)) →
    ((1 + 7 * (i : ℕ) = 8 ∧ 1 + 7 * (j : ℕ) = 29) ∨ (1 + 7 * (i : ℕ) = 29 ∧ 1 + 7 * (j : ℕ) = 8) ∨
     (1 + 7 * (i : ℕ) = 15 ∧ 1 + 7 * (j : ℕ) = 29) ∨
     (1 + 7 * (i : ℕ) = 29 ∧ 1 + 7 * (j : ℕ) = 15)) := by
  decide

-- Case `r = 3`: the double `{8, 29}`; the other candidates form two 5-cycles.
def v3a : Fin 5 → Fin 35 := ![23, 4, 3, 31, 12]
def v3b : Fin 5 → Fin 35 := ![17, 33, 26, 25, 6]

theorem v3a_adj : ∀ i : Fin 5, v3a i ≠ v3a (i + 1) ∧ kadj (v3a i : ℕ) (v3a (i + 1) : ℕ) := by
  decide

theorem v3b_adj : ∀ i : Fin 5, v3b i ≠ v3b (i + 1) ∧ kadj (v3b i : ℕ) (v3b (i + 1) : ℕ) := by
  decide

theorem cand3 : ∀ w : Fin 35, ¬ kadj (w : ℕ) 0 → ¬ kadj (w : ℕ) 21 → ¬ kadj (w : ℕ) 8 →
    ¬ kadj (w : ℕ) 29 →
    w ∈ ({0, 21, 8, 29} : Finset (Fin 35)) ∨ w ∈ Finset.univ.image v3a ∨
      w ∈ Finset.univ.image v3b := by
  decide

-- Case `r = 4`: the double `{29, 15}`; the other candidates form a 5-cycle and two edges.
def v4 : Fin 5 → Fin 35 := ![9, 25, 6, 17, 33]

theorem v4_adj : ∀ i : Fin 5, v4 i ≠ v4 (i + 1) ∧ kadj (v4 i : ℕ) (v4 (i + 1) : ℕ) := by
  decide

theorem e4a_adj : kadj 12 23 := by decide
theorem e4b_adj : kadj 27 3 := by decide

theorem cand4 : ∀ w : Fin 35, ¬ kadj (w : ℕ) 0 → ¬ kadj (w : ℕ) 21 → ¬ kadj (w : ℕ) 29 →
    ¬ kadj (w : ℕ) 15 →
    w ∈ ({0, 21, 29, 15} : Finset (Fin 35)) ∨ w ∈ Finset.univ.image v4 ∨
      w ∈ ({12, 23} : Finset (Fin 35)) ∨ w ∈ ({27, 3} : Finset (Fin 35)) := by
  decide

-- Counting helpers.
theorem card_filter_mem_le {I A : Finset (Fin 35)} : (I.filter (fun x => x ∈ A)).card ≤ A.card :=
  Finset.card_le_card (fun _ hx => (Finset.mem_filter.mp hx).2)

theorem edge_card_le {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y) (u w : Fin 35)
    (huw : u ≠ w) (h : kadj (u : ℕ) (w : ℕ)) :
    (I.filter (fun x => x ∈ ({u, w} : Finset (Fin 35)))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx hy
  by_contra hne
  have hn := indep_kadj hI
  rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
  · exact hne rfl
  · exact hn _ hx.1 _ hy.1 huw h
  · exact hn _ hy.1 _ hx.1 huw h
  · exact hne rfl

theorem cyc_adj {v : Fin 5 → Fin 35}
    (h : ∀ i : Fin 5, v i ≠ v (i + 1) ∧ kadj (v i : ℕ) (v (i + 1) : ℕ)) :
    ∀ i, kg.Adj (v i) (v (i + 1)) := fun i => (kg_adj _ _).mpr (h i)

theorem norm3 {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y)
    (h0 : (0 : Fin 35) ∈ I) (h21 : (21 : Fin 35) ∈ I) (h8 : (8 : Fin 35) ∈ I)
    (h29 : (29 : Fin 35) ∈ I) : I.card ≤ 8 := by
  have hn := indep_kadj hI
  have hsub : I ⊆ I.filter (fun x => x ∈ ({0, 21, 8, 29} : Finset (Fin 35))) ∪
      I.filter (fun x => x ∈ Finset.univ.image v3a) ∪
      I.filter (fun x => x ∈ Finset.univ.image v3b) := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hA : w ∈ ({0, 21, 8, 29} : Finset (Fin 35))
    · exact Or.inl (Or.inl ⟨hw, hA⟩)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hA
      rcases cand3 w (hn w hw 0 h0 hA.1) (hn w hw 21 h21 hA.2.1) (hn w hw 8 h8 hA.2.2.1)
          (hn w hw 29 h29 hA.2.2.2) with h | h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp_all
      · exact Or.inl (Or.inr ⟨hw, h⟩)
      · exact Or.inr ⟨hw, h⟩
  have c1 : (I.filter (fun x => x ∈ ({0, 21, 8, 29} : Finset (Fin 35)))).card ≤ 4 :=
    card_filter_mem_le.trans (by decide)
  have c2 := cycle5 hI v3a (cyc_adj v3a_adj)
  have c3 := cycle5 hI v3b (cyc_adj v3b_adj)
  calc I.card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 4 + 2 + 2 := by omega
    _ = 8 := rfl

theorem norm4 {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y)
    (h0 : (0 : Fin 35) ∈ I) (h21 : (21 : Fin 35) ∈ I) (h29 : (29 : Fin 35) ∈ I)
    (h15 : (15 : Fin 35) ∈ I) : I.card ≤ 8 := by
  have hn := indep_kadj hI
  have hsub : I ⊆ I.filter (fun x => x ∈ ({0, 21, 29, 15} : Finset (Fin 35))) ∪
      I.filter (fun x => x ∈ Finset.univ.image v4) ∪
      I.filter (fun x => x ∈ ({12, 23} : Finset (Fin 35))) ∪
      I.filter (fun x => x ∈ ({27, 3} : Finset (Fin 35))) := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hA : w ∈ ({0, 21, 29, 15} : Finset (Fin 35))
    · exact Or.inl (Or.inl (Or.inl ⟨hw, hA⟩))
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hA
      rcases cand4 w (hn w hw 0 h0 hA.1) (hn w hw 21 h21 hA.2.1) (hn w hw 29 h29 hA.2.2.1)
          (hn w hw 15 h15 hA.2.2.2) with h | h | h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp_all
      · exact Or.inl (Or.inl (Or.inr ⟨hw, h⟩))
      · exact Or.inl (Or.inr ⟨hw, h⟩)
      · exact Or.inr ⟨hw, h⟩
  have c1 : (I.filter (fun x => x ∈ ({0, 21, 29, 15} : Finset (Fin 35)))).card ≤ 4 :=
    card_filter_mem_le.trans (by decide)
  have c2 := cycle5 hI v4 (cyc_adj v4_adj)
  have c3 := edge_card_le hI 12 23 (by decide) e4a_adj
  have c4 := edge_card_le hI 27 3 (by decide) e4b_adj
  calc I.card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ 4 + 2 + 1 + 1 := by omega
    _ = 8 := rfl

-- The normalised statement: `0, 21 ∈ I` and two distinct elements of layer `1`.
theorem norm_card_le {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y)
    (h0 : (0 : Fin 35) ∈ I) (h21 : (21 : Fin 35) ∈ I) (y z : Fin 35) (hy : y ∈ I) (hz : z ∈ I)
    (hyz : y ≠ z) (hy7 : (y : ℕ) % 7 = 1) (hz7 : (z : ℕ) % 7 = 1) : I.card ≤ 8 := by
  have hn := indep_kadj hI
  have hy' : (y : ℕ) = 1 + 7 * ((y : ℕ) / 7) := by omega
  have hz' : (z : ℕ) = 1 + 7 * ((z : ℕ) / 7) := by omega
  have hij : (⟨(y : ℕ) / 7, by omega⟩ : Fin 5) ≠ ⟨(z : ℕ) / 7, by omega⟩ := by
    intro h
    apply hyz
    apply Fin.ext
    have := congrArg Fin.val h
    simp only at this
    omega
  have ny0 := hn y hy 0 h0 (by intro h; rw [h] at hy7; exact absurd hy7 (by decide))
  have ny21 := hn y hy 21 h21 (by intro h; rw [h] at hy7; exact absurd hy7 (by decide))
  have nz0 := hn z hz 0 h0 (by intro h; rw [h] at hz7; exact absurd hz7 (by decide))
  have nz21 := hn z hz 21 h21 (by intro h; rw [h] at hz7; exact absurd hz7 (by decide))
  have nyz := hn y hy z hz hyz
  have t := layer1_table ⟨(y : ℕ) / 7, by omega⟩ ⟨(z : ℕ) / 7, by omega⟩ hij
    (by simp only; rw [← hy']; exact ny0) (by simp only; rw [← hy']; exact ny21)
    (by simp only; rw [← hz']; exact nz0) (by simp only; rw [← hz']; exact nz21)
    (by simp only; rw [← hy', ← hz']; exact nyz)
  simp only at t
  rw [← hy', ← hz'] at t
  rcases t with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have ey : y = 8 := Fin.ext e1
    have ez : z = 29 := Fin.ext e2
    subst ey ez; exact norm3 hI h0 h21 hy hz
  · have ey : y = 29 := Fin.ext e1
    have ez : z = 8 := Fin.ext e2
    subst ey ez; exact norm3 hI h0 h21 hz hy
  · have ey : y = 15 := Fin.ext e1
    have ez : z = 29 := Fin.ext e2
    subst ey ez; exact norm4 hI h0 h21 hz hy
  · have ey : y = 29 := Fin.ext e1
    have ez : z = 15 := Fin.ext e2
    subst ey ez; exact norm4 hI h0 h21 hy hz


-- The automorphisms `x ↦ q (x - t)` for `q ∈ {1, 11, 16}` (the units that fix the connection set).
def σ (q t : ℕ) (x : Fin 35) : Fin 35 := ⟨(q * ((x : ℕ) + 35 - t)) % 35, Nat.mod_lt _ (by norm_num)⟩

theorem S35_mul : ∀ q ∈ ({1, 11, 16} : Finset ℕ), ∀ s < 35, ((q * s) % 35 ∈ S35 ↔ s ∈ S35) := by
  decide

theorem σ_sd {q : ℕ} (hq : q ∈ ({1, 11, 16} : Finset ℕ)) {t : ℕ} (ht : t < 35) (x y : Fin 35) :
    sd (σ q t x : ℕ) (σ q t y : ℕ) = (q * sd (x : ℕ) (y : ℕ)) % 35 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  have hx := x.isLt
  have hy := y.isLt
  simp only [σ, sd]
  rcases hq with rfl | rfl | rfl <;> omega

theorem σ_kadj {q : ℕ} (hq : q ∈ ({1, 11, 16} : Finset ℕ)) {t : ℕ} (ht : t < 35) (x y : Fin 35) :
    kadj (σ q t x : ℕ) (σ q t y : ℕ) ↔ kadj (x : ℕ) (y : ℕ) := by
  unfold kadj
  have h1 := S35_mul q hq (sd (x : ℕ) (y : ℕ)) (by unfold sd; exact Nat.mod_lt _ (by norm_num))
  have h2 := S35_mul q hq (sd (y : ℕ) (x : ℕ)) (by unfold sd; exact Nat.mod_lt _ (by norm_num))
  rw [σ_sd hq ht x y, σ_sd hq ht y x, h1, h2]

theorem σ_inj {q : ℕ} (hq : q ∈ ({1, 11, 16} : Finset ℕ)) {t : ℕ} (ht : t < 35) {x y : Fin 35}
    (h : σ q t x = σ q t y) : x = y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  have hx := x.isLt
  have hy := y.isLt
  have := congrArg Fin.val h
  simp only [σ] at this
  apply Fin.ext
  rcases hq with rfl | rfl | rfl <;> omega

-- Applying an automorphism keeps the set independent and its size.
theorem image_indep {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y) {q : ℕ}
    (hq : q ∈ ({1, 11, 16} : Finset ℕ)) {t : ℕ} (ht : t < 35) :
    ∀ x ∈ I.image (σ q t), ∀ y ∈ I.image (σ q t), ¬ kg.Adj x y := by
  intro x hx y hy hadj
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
  rw [kg_adj] at hadj
  exact hI x' hx' y' hy' ((kg_adj _ _).mpr ⟨fun h => hadj.1 (h ▸ rfl), (σ_kadj hq ht _ _).mp hadj.2⟩)

-- Two doubles at layers `b₁ ≠ b₂` with the base pair `x₁, x₁ + 21` and the multiplier `q`
-- chosen so that layer `b₂` goes to layer `1`.
theorem two_doubles {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y)
    (x₁ z₁ : Fin 35) (hx₁ : x₁ ∈ I) (hz₁ : z₁ ∈ I) (h21 : sd (x₁ : ℕ) (z₁ : ℕ) = 21)
    (y₂ z₂ : Fin 35) (hy₂ : y₂ ∈ I) (hz₂ : z₂ ∈ I) (hne : y₂ ≠ z₂)
    (hl : (y₂ : ℕ) % 7 = (z₂ : ℕ) % 7) (q : ℕ) (hq : q ∈ ({1, 11, 16} : Finset ℕ))
    (hd : (q * ((y₂ : ℕ) + 35 - (x₁ : ℕ))) % 7 = 1) : I.card ≤ 8 := by
  have hcard : (I.image (σ q (x₁ : ℕ))).card = I.card :=
    Finset.card_image_of_injOn (fun _ _ _ _ h => σ_inj hq x₁.isLt h)
  rw [← hcard]
  have hq' := hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
  have hx1 := x₁.isLt
  have hz1 := z₁.isLt
  have hy2 := y₂.isLt
  have hz2 := z₂.isLt
  refine norm_card_le (image_indep hI hq x₁.isLt) ?_ ?_ (σ q x₁ y₂) (σ q x₁ z₂)
    (Finset.mem_image_of_mem _ hy₂) (Finset.mem_image_of_mem _ hz₂)
    (fun h => hne (σ_inj hq x₁.isLt h)) ?_ ?_
  · refine Finset.mem_image.mpr ⟨x₁, hx₁, ?_⟩
    apply Fin.ext; simp only [σ]; rcases hq' with rfl | rfl | rfl <;> omega
  · refine Finset.mem_image.mpr ⟨z₁, hz₁, ?_⟩
    apply Fin.ext; simp only [σ, sd] at h21 ⊢; rcases hq' with rfl | rfl | rfl <;> omega
  · simp only [σ]; rcases hq' with rfl | rfl | rfl <;> omega
  · simp only [σ]; rcases hq' with rfl | rfl | rfl <;> omega

-- Choosing the base pair and the multiplier.
theorem two_doubles' {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y)
    (x₁ z₁ : Fin 35) (hx₁ : x₁ ∈ I) (hz₁ : z₁ ∈ I) (h1 : x₁ ≠ z₁)
    (hl1 : (x₁ : ℕ) % 7 = (z₁ : ℕ) % 7)
    (y₂ z₂ : Fin 35) (hy₂ : y₂ ∈ I) (hz₂ : z₂ ∈ I) (hne : y₂ ≠ z₂)
    (hl : (y₂ : ℕ) % 7 = (z₂ : ℕ) % 7)
    (hQ : ((y₂ : ℕ) + 35 - (x₁ : ℕ)) % 7 = 1 ∨ ((y₂ : ℕ) + 35 - (x₁ : ℕ)) % 7 = 2 ∨
      ((y₂ : ℕ) + 35 - (x₁ : ℕ)) % 7 = 4) : I.card ≤ 8 := by
  have hn := indep_kadj hI x₁ hx₁ z₁ hz₁ h1
  have hx1 := x₁.isLt
  have hz1 := z₁.isLt
  have hy2 := y₂.isLt
  -- the base pair is at cyclic distance `14` or `21`
  have h14 : sd (x₁ : ℕ) (z₁ : ℕ) = 21 ∨ sd (z₁ : ℕ) (x₁ : ℕ) = 21 := by
    unfold kadj at hn
    simp only [S35, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hne' : (x₁ : ℕ) ≠ (z₁ : ℕ) := fun h => h1 (Fin.ext h)
    unfold sd at hn ⊢
    omega
  rcases h14 with h14 | h14
  · rcases hQ with hd | hd | hd
    · exact two_doubles hI x₁ z₁ hx₁ hz₁ h14 y₂ z₂ hy₂ hz₂ hne hl 1 (by decide) (by omega)
    · exact two_doubles hI x₁ z₁ hx₁ hz₁ h14 y₂ z₂ hy₂ hz₂ hne hl 11 (by decide) (by omega)
    · exact two_doubles hI x₁ z₁ hx₁ hz₁ h14 y₂ z₂ hy₂ hz₂ hne hl 16 (by decide) (by omega)
  · rcases hQ with hd | hd | hd
    · exact two_doubles hI z₁ x₁ hz₁ hx₁ h14 y₂ z₂ hy₂ hz₂ hne hl 1 (by decide) (by omega)
    · exact two_doubles hI z₁ x₁ hz₁ hx₁ h14 y₂ z₂ hy₂ hz₂ hne hl 11 (by decide) (by omega)
    · exact two_doubles hI z₁ x₁ hz₁ hx₁ h14 y₂ z₂ hy₂ hz₂ hne hl 16 (by decide) (by omega)

-- At most one layer has two elements, so the seven layers hold at most `7 + 1` vertices.
theorem sum_layers_le (c : ℕ → ℕ) (h2 : ∀ b, b < 7 → c b ≤ 2)
    (hd : ∀ b₁, b₁ < 7 → ∀ b₂, b₂ < 7 → b₁ ≠ b₂ → c b₁ = 2 → c b₂ = 2 → False) :
    ∑ b ∈ Finset.range 7, c b ≤ 8 := by
  have hD1 : ((Finset.range 7).filter (fun b => c b = 2)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    by_contra hne
    exact hd a ha.1 b hb.1 hne ha.2 hb.2
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range 7) (fun b => c b = 2) c
  have hA : ∑ b ∈ (Finset.range 7).filter (fun b => c b = 2), c b ≤
      ((Finset.range 7).filter (fun b => c b = 2)).card • 2 := by
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro b hb; rw [Finset.mem_filter] at hb; omega
  have hB : ∑ b ∈ (Finset.range 7).filter (fun b => ¬ c b = 2), c b ≤
      ((Finset.range 7).filter (fun b => ¬ c b = 2)).card • 1 := by
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro b hb; rw [Finset.mem_filter, Finset.mem_range] at hb; have := h2 b hb.1; omega
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.range 7) (fun b => c b = 2)
  rw [Finset.card_range] at hcard
  simp only [smul_eq_mul] at hA hB
  omega

-- Every independent set of the Kalbfleisch graph has at most `8` vertices.
theorem kg_indep_card_le {I : Finset (Fin 35)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ kg.Adj x y) :
    I.card ≤ 8 := by
  have hlay := layer_card_le hI
  by_cases hd : ∃ b₁, b₁ < 7 ∧ ∃ b₂, b₂ < 7 ∧ b₁ ≠ b₂ ∧
      (I.filter (fun x : Fin 35 => (x : ℕ) % 7 = b₁)).card = 2 ∧
      (I.filter (fun x : Fin 35 => (x : ℕ) % 7 = b₂)).card = 2
  · obtain ⟨b₁, hb₁, b₂, hb₂, hne, c₁, c₂⟩ := hd
    obtain ⟨x₁, z₁, h1, e1⟩ := Finset.card_eq_two.mp c₁
    obtain ⟨y₂, z₂, h2, e2⟩ := Finset.card_eq_two.mp c₂
    have m1 : x₁ ∈ I ∧ (x₁ : ℕ) % 7 = b₁ := Finset.mem_filter.mp (e1 ▸ Finset.mem_insert_self _ _)
    have m1' : z₁ ∈ I ∧ (z₁ : ℕ) % 7 = b₁ :=
      Finset.mem_filter.mp (e1 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have m2 : y₂ ∈ I ∧ (y₂ : ℕ) % 7 = b₂ := Finset.mem_filter.mp (e2 ▸ Finset.mem_insert_self _ _)
    have m2' : z₂ ∈ I ∧ (z₂ : ℕ) % 7 = b₂ :=
      Finset.mem_filter.mp (e2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hx1 := x₁.isLt
    have hy2 := y₂.isLt
    -- either `b₂ - b₁` or `b₁ - b₂` is a quadratic residue mod 7
    by_cases hQ : ((y₂ : ℕ) + 35 - (x₁ : ℕ)) % 7 = 1 ∨ ((y₂ : ℕ) + 35 - (x₁ : ℕ)) % 7 = 2 ∨
        ((y₂ : ℕ) + 35 - (x₁ : ℕ)) % 7 = 4
    · exact two_doubles' hI x₁ z₁ m1.1 m1'.1 h1 (by omega) y₂ z₂ m2.1 m2'.1 h2 (by omega) hQ
    · refine two_doubles' hI y₂ z₂ m2.1 m2'.1 h2 (by omega) x₁ z₁ m1.1 m1'.1 h1 (by omega) ?_
      omega
  · rw [card_eq_sum_layers I]
    refine sum_layers_le _ hlay ?_
    intro b₁ hb₁ b₂ hb₂ hne e1 e2
    exact hd ⟨b₁, hb₁, b₂, hb₂, hne, e1, e2⟩

theorem good_k35 : Good 35 8 :=
  ⟨kg, kg_cliqueFree, fun _ hT => kg_indep_card_le hT⟩


-- The pieces for the remainder: `q` copies of the 35-vertex graph, then `13⌊r/4⌋` and one of
-- the small graphs.
theorem good_k35_mul (q : ℕ) : Good (35 * q) (8 * q) := by
  induction q with
  | zero => exact good_c5 0
  | succ n ih =>
    have h := good_union ih good_k35
    rw [show 35 * (n + 1) = 35 * n + 35 by ring, show 8 * (n + 1) = 8 * n + 8 by ring]
    exact h

theorem good_rem4 (r : ℕ) (hr : r < 4) : Good (if r = 0 then 0 else 3 * r - 1) r := by
  interval_cases r
  · simpa using good_c5 0
  · simpa using good_c5 1
  · simpa using good_c5 2
  · simpa using good_wagner

theorem good_rem (r : ℕ) : Good (rem r) r := by
  have h1 : Good (13 * (r / 4)) (4 * (r / 4)) := by
    have := good_c13 (4 * (r / 4))
    rwa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4), Nat.mul_mod_right, Nat.mul_zero,
      Nat.add_zero] at this
  have h2 := good_rem4 (r % 4) (Nat.mod_lt _ (by norm_num))
  have h3 := good_union h1 h2
  rw [Nat.div_add_mod] at h3
  exact h3

theorem good_base (m : ℕ) : Good (base m) m := by
  have h := good_union (good_k35_mul (m / 8)) (good_rem (m % 8))
  rw [Nat.div_add_mod] at h
  exact h

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
  · have hc := hGi T (SqueezeBench.Ramsey3.Lower.V005.indep_of_isClique_compl hT.isClique)
    rw [hT.card_eq] at hc
    omega

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f v :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey3.Lower.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V005.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V005.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Ramsey3.Lower.V006
