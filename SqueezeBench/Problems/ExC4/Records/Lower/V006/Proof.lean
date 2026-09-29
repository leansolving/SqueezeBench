import SqueezeBench.Problems.ExC4.Records.Lower.V006.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V005.Proof

/-! Record V006 for ExC4, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V006.lean`. -/

namespace SqueezeBench.ExC4.Lower.V006

open Finset SimpleGraph SqueezeBench.ExC4

/-! ### The polarity graph `ER_q` over an arbitrary finite field, in affine coordinates -/

section ERdef
variable (F : Type) [Field F]

-- Vertices: the affine points `(a, b)`, the points at infinity `some m`, and `none`.
abbrev ERV := (F × F) ⊕ Option F

-- `(a,b) ~ (c,d)` iff `ac = b + d`; `(a,b) ~ some a`; `some m ~ none`. This is the orthogonal
-- polarity of `PG(2, F)` for the form `x x' - y z' - z y'`, written without projective points.
def erAdj : ERV F → ERV F → Prop
  | Sum.inl (a, b), Sum.inl (c, d) => (a, b) ≠ (c, d) ∧ a * c = b + d
  | Sum.inl (a, _), Sum.inr (some m) => a = m
  | Sum.inr (some m), Sum.inl (a, _) => a = m
  | Sum.inr (some _), Sum.inr none => True
  | Sum.inr none, Sum.inr (some _) => True
  | _, _ => False

theorem erAdj_symm : ∀ x y, erAdj F x y → erAdj F y x := by
  rintro (⟨a, b⟩ | (m | _)) (⟨c, d⟩ | (m' | _)) h <;> simp only [erAdj] at h ⊢
  · refine ⟨fun h' => h.1 h'.symm, ?_⟩
    rw [mul_comm, add_comm]; exact h.2
  · exact h
  · exact h

theorem erAdj_irrefl : ∀ x, ¬ erAdj F x x := by
  rintro (⟨a, b⟩ | (m | _)) h <;> simp only [erAdj] at h
  exact h.1 rfl

def ER : SimpleGraph (ERV F) where
  Adj := erAdj F
  symm := ⟨erAdj_symm F⟩
  loopless := ⟨erAdj_irrefl F⟩

-- Two distinct vertices have at most one common neighbour: for two affine points this is the
-- linear system `(a - c) e = b - d`, and the other cases are immediate.
theorem ER_free : NoTwoCommonNeighbours (ER F) := by
  rintro (⟨a, b⟩ | (m | _)) (⟨c, d⟩ | (m' | _)) (⟨e, g⟩ | (k | _)) (⟨h, i⟩ | (k' | _))
    hxy huv hxu hyu hxv hyv <;>
    simp only [ER, erAdj, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
      Option.some.injEq, not_and] at hxy huv hxu hyu hxv hyv
  all_goals try subst_vars
  all_goals try simp_all
  all_goals
    have hkey : (a - c) * (e - h) = 0 := by linear_combination hxu.2 - hyu.2 - hxv.2 + hyv.2
    rcases mul_eq_zero.1 hkey with h1 | h1
    · have hac : a = c := sub_eq_zero.1 h1
      subst hac
      exact hxy rfl (add_right_cancel (hxu.2.symm.trans hyu.2))
    · have heh : e = h := sub_eq_zero.1 h1
      subst heh
      exact huv rfl (add_left_cancel (hxu.2.symm.trans hxv.2))

theorem ER_adj_inl_some {a b m : F} :
    (ER F).Adj (Sum.inl (a, b)) (Sum.inr (some m)) ↔ a = m := Iff.rfl
theorem ER_adj_some_inl {a b m : F} :
    (ER F).Adj (Sum.inr (some m)) (Sum.inl (a, b)) ↔ a = m := Iff.rfl
theorem ER_adj_some_none {m : F} : (ER F).Adj (Sum.inr (some m)) (Sum.inr none) := trivial
theorem ER_adj_none_some {m : F} : (ER F).Adj (Sum.inr none) (Sum.inr (some m)) := trivial

end ERdef

section ERcount
variable (F : Type) [Field F] [Fintype F] [DecidableEq F]

instance : DecidableRel (erAdj F) := by
  rintro (⟨a, b⟩ | (m | _)) (⟨c, d⟩ | (m' | _)) <;> simp only [erAdj] <;> infer_instance

instance : DecidableRel (ER F).Adj := inferInstanceAs (DecidableRel (erAdj F))

-- `none` sees every `some m`.
theorem deg_none : Fintype.card F ≤ (ER F).degree (Sum.inr none) := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : (univ : Finset F).image (fun m => (Sum.inr (some m) : ERV F))
      ⊆ (ER F).neighborFinset (Sum.inr none) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨m, -, rfl⟩ := hx
    rw [mem_neighborFinset]
    exact ER_adj_none_some F
  have hcard : #((univ : Finset F).image (fun m => (Sum.inr (some m) : ERV F)))
      = Fintype.card F := by
    rw [card_image_of_injective _ (fun x y h => by simpa using h), card_univ]
  rw [← hcard]; exact card_le_card hsub

-- `some m` sees the column `a = m` and `none`.
theorem deg_some (m : F) : Fintype.card F + 1 ≤ (ER F).degree (Sum.inr (some m)) := by
  rw [← card_neighborFinset_eq_degree]
  set T := (univ : Finset F).image (fun d => (Sum.inl (m, d) : ERV F)) with hT
  have hsub : T ∪ {Sum.inr none} ⊆ (ER F).neighborFinset (Sum.inr (some m)) := by
    intro x hx
    rw [mem_union, mem_singleton, hT, mem_image] at hx
    rw [mem_neighborFinset]
    rcases hx with ⟨d, -, rfl⟩ | rfl
    · exact (ER_adj_some_inl F).2 rfl
    · exact ER_adj_some_none F
  have hdisj : Disjoint T {Sum.inr none} := by
    rw [disjoint_singleton_right, hT, mem_image]
    rintro ⟨d, -, h⟩
    exact Sum.inl_ne_inr h
  have hcard : #T = Fintype.card F := by
    rw [hT, card_image_of_injective _ (fun x y h => by simpa using h), card_univ]
  calc Fintype.card F + 1 = #(T ∪ {Sum.inr none}) := by
        rw [card_union_of_disjoint hdisj, hcard, card_singleton]
    _ ≤ _ := card_le_card hsub

-- `(a, b)` sees the `q` points `(c, ac - b)`, minus itself when `a² = 2b`, plus `some a`.
theorem deg_inl (a b : F) :
    Fintype.card F + 1 ≤ (ER F).degree (Sum.inl (a, b)) + (if a * a = b + b then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree]
  set S := (univ : Finset F).image (fun c => (Sum.inl (c, a * c - b) : ERV F)) with hS
  have hSc : #S = Fintype.card F := by
    rw [hS, card_image_of_injective _ (fun x y h => (Prod.mk.inj (Sum.inl.inj h)).1), card_univ]
  have hmem : Sum.inl (a, b) ∈ S ↔ a * a = b + b := by
    rw [hS, mem_image]
    constructor
    · rintro ⟨c, -, h⟩
      obtain ⟨rfl, h2⟩ := Prod.mk.inj (Sum.inl.inj h)
      exact sub_eq_iff_eq_add.1 h2
    · intro h
      exact ⟨a, mem_univ _, by rw [h, add_sub_cancel_right]⟩
  have hsub : (S.erase (Sum.inl (a, b))) ∪ {Sum.inr (some a)}
      ⊆ (ER F).neighborFinset (Sum.inl (a, b)) := by
    intro x hx
    rw [mem_union, mem_singleton, mem_erase, hS, mem_image] at hx
    rw [mem_neighborFinset]
    rcases hx with ⟨hne, c, -, rfl⟩ | rfl
    · exact ⟨fun h => hne (congrArg Sum.inl h.symm), by rw [add_sub_cancel]⟩
    · exact (ER_adj_inl_some F).2 rfl
  have hdisj : Disjoint (S.erase (Sum.inl (a, b))) {Sum.inr (some a)} := by
    rw [disjoint_singleton_right, mem_erase, hS, mem_image]
    rintro ⟨-, c, -, h⟩
    exact Sum.inl_ne_inr h
  have hle := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_singleton, card_erase_eq_ite, hSc] at hle
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  by_cases hl : a * a = b + b
  · rw [if_pos (hmem.2 hl)] at hle
    rw [if_pos hl]
    omega
  · rw [if_neg (fun h => hl (hmem.1 h))] at hle
    rw [if_neg hl]
    omega

-- At most `q` absolute affine points: `a² = 2b` determines `b` from `a` in odd characteristic,
-- and forces `a = 0` in characteristic two.
theorem card_loops_le :
    #((univ : Finset (F × F)).filter (fun x => x.1 * x.1 = x.2 + x.2)) ≤ Fintype.card F := by
  by_cases h2 : (2 : F) = 0
  · calc _ ≤ #(univ : Finset F) := card_le_card_of_injOn Prod.snd (fun _ _ => mem_univ _) ?_
      _ = _ := card_univ
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx hy
    have hx1 : x.1 = 0 := mul_self_eq_zero.1 (by rw [hx, ← two_mul, h2, zero_mul])
    have hy1 : y.1 = 0 := mul_self_eq_zero.1 (by rw [hy, ← two_mul, h2, zero_mul])
    exact Prod.ext (hx1.trans hy1.symm) hxy
  · calc _ ≤ #(univ : Finset F) := card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_
      _ = _ := card_univ
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx hy
    have : (2 : F) * x.2 = 2 * y.2 := by rw [two_mul, two_mul, ← hx, ← hy, hxy]
    exact Prod.ext hxy (mul_left_cancel₀ h2 this)

-- Degree sum: `q² (q + 1) - q + q (q + 1) + q = q (q + 1)²`.
theorem ER_edges :
    Fintype.card F * (Fintype.card F + 1) * (Fintype.card F + 1) ≤ 2 * #(ER F).edgeFinset := by
  rw [← sum_degrees_eq_twice_card_edges, Fintype.sum_sum_type, Fintype.sum_option]
  have hsum1 : ∑ x : F × F, (Fintype.card F + 1) ≤
      ∑ x : F × F, ((ER F).degree (Sum.inl x) + (if x.1 * x.1 = x.2 + x.2 then 1 else 0)) :=
    sum_le_sum (fun x _ => deg_inl F x.1 x.2)
  rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul, sum_add_distrib, sum_boole,
    Nat.cast_id] at hsum1
  have hL := card_loops_le F
  have hsum2 : ∑ m : F, (Fintype.card F + 1) ≤ ∑ m : F, (ER F).degree (Sum.inr (some m)) :=
    sum_le_sum (fun m _ => deg_some F m)
  rw [sum_const, card_univ, smul_eq_mul] at hsum2
  have h3 := deg_none F
  nlinarith [hsum1, hL, hsum2, h3]

end ERcount

theorem ER_card (F : Type) [Fintype F] :
    Fintype.card (ERV F) = Fintype.card F * Fintype.card F + Fintype.card F + 1 := by
  simp only [ERV, Fintype.card_sum, Fintype.card_prod, Fintype.card_option]
  ring

/-! ### Transport lemmas -/

theorem noTwo_map {V W : Type*} (e : V ↪ W) {G : SimpleGraph V} (h : NoTwoCommonNeighbours G) :
    NoTwoCommonNeighbours (G.map e) := by
  intro x y u w hxy huw hxu hyu hxw hyw
  rw [map_adj] at hxu hyu hxw hyw
  obtain ⟨x₁, u₁, h1, rfl, rfl⟩ := hxu
  obtain ⟨y₁, u₂, h2, rfl, hu⟩ := hyu
  obtain ⟨x₂, w₁, h3, hx, rfl⟩ := hxw
  obtain ⟨y₂, w₂, h4, hy, hw⟩ := hyw
  obtain rfl := e.injective hu
  obtain rfl := e.injective hx
  obtain rfl := e.injective hy
  obtain rfl := e.injective hw
  exact h _ _ _ _ (fun h' => hxy (by rw [h'])) (fun h' => huw (by rw [h'])) h1 h2 h3 h4

-- `f (q² + q + 1) ≥ q (q + 1)² / 2` for every finite field of order `q`.
theorem er_bound (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F * (Fintype.card F + 1) * (Fintype.card F + 1) / 2 ≤
      f (Fintype.card F * Fintype.card F + Fintype.card F + 1) := by
  let e := Fintype.equivFin (ERV F)
  let G : SimpleGraph (Fin (Fintype.card (ERV F))) := (ER F).map e.toEmbedding
  have hfree : NoTwoCommonNeighbours G := noTwo_map _ (ER_free F)
  have hle : #G.edgeFinset ≤ f (Fintype.card (ERV F)) :=
    le_f_of_noTwoCommonNeighbours (by rw [ER_card, nMin_eq]; omega) hfree
  have hle' : #G.edgeFinset ≤ f (Fintype.card F * Fintype.card F + Fintype.card F + 1) := by
    rw [← ER_card]; exact hle
  have hG : #G.edgeFinset = #(ER F).edgeFinset := card_edgeFinset_map _ _
  have h2 := ER_edges F
  generalize Fintype.card F * (Fintype.card F + 1) * (Fintype.card F + 1) = P at *
  omega

-- Every prime power `q = p ^ k` is the order of a finite field, `GaloisField p k`.
theorem er_primePow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k * (p ^ k + 1) * (p ^ k + 1) / 2 ≤ f (p ^ k * p ^ k + p ^ k + 1) := by
  haveI := Fact.mk hp
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField p k) := Classical.decEq _
  have hc : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
  have := er_bound (GaloisField p k)
  rwa [hc] at this

/-! ### General facts about `f`: extremal graphs, superadditivity, vertex deletion -/

theorem f_zero : f 0 = 0 := by simp [f, nMin]

-- A `C₄`-free graph on `n` vertices with at least `f n` edges.
theorem exists_graph (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      NoTwoCommonNeighbours G ∧ f n ≤ #G.edgeFinset := by
  rcases Nat.eq_zero_or_pos (f n) with h0 | hpos
  · exact ⟨⊥, inferInstance, fun _ _ _ _ _ _ h => by simp at h, by rw [h0]; exact Nat.zero_le _⟩
  · have hn' : nMin ≤ n := by rw [nMin_eq]; exact hn
    have hf : f n = extremalNumber n (cycleGraph 4) := by rw [f, if_neg (Nat.not_lt.mpr hn')]
    have hlt : f n - 1 < extremalNumber (Fintype.card (Fin n)) (cycleGraph 4) := by
      rw [Fintype.card_fin]; omega
    obtain ⟨G, inst, hfree, hG⟩ :=
      (lt_extremalNumber_iff (V := Fin n) (cycleGraph 4) (f n - 1)).1 hlt
    exact ⟨G, inst, (free_cycleGraph_four_iff G).1 hfree, by omega⟩

instance sumDecidableRel {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  rintro (x | x) (y | y) <;> simp only [sum_adj] <;> infer_instance

theorem noTwo_sum {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : NoTwoCommonNeighbours G) (hH : NoTwoCommonNeighbours H) :
    NoTwoCommonNeighbours (G ⊕g H) := by
  rintro (x | x) (y | y) (u | u) (w | w) hxy huw hxu hyu hxw hyw <;>
    simp only [sum_adj] at hxu hyu hxw hyw
  · exact hG x y u w (fun h => hxy (by rw [h])) (fun h => huw (by rw [h])) hxu hyu hxw hyw
  · exact hH x y u w (fun h => hxy (by rw [h])) (fun h => huw (by rw [h])) hxu hyu hxw hyw

theorem card_edgeFinset_sum_ge {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel H.Adj] [DecidableRel (G ⊕g H).Adj] :
    #G.edgeFinset + #H.edgeFinset ≤ #(G ⊕g H).edgeFinset := by
  have hsub : G.edgeFinset.image (Sym2.map Sum.inl) ∪ H.edgeFinset.image (Sym2.map Sum.inr)
      ⊆ (G ⊕g H).edgeFinset := by
    intro s hs
    rw [mem_union, mem_image, mem_image] at hs
    rcases hs with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
    · revert hs'
      refine Sym2.ind (fun x y hs' => ?_) s'
      rw [mem_edgeFinset, mem_edgeSet] at hs'
      rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet]
      simpa [sum_adj] using hs'
    · revert hs'
      refine Sym2.ind (fun x y hs' => ?_) s'
      rw [mem_edgeFinset, mem_edgeSet] at hs'
      rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet]
      simpa [sum_adj] using hs'
  have hdisj : Disjoint (G.edgeFinset.image (Sym2.map Sum.inl))
      (H.edgeFinset.image (Sym2.map Sum.inr)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [mem_image] at hs hs'
    obtain ⟨a, -, rfl⟩ := hs
    obtain ⟨b, -, hb⟩ := hs'
    revert hb
    refine Sym2.ind (fun x y => Sym2.ind (fun x' y' hb => ?_) a) b
    rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at hb
    rcases hb with ⟨h, -⟩ | ⟨h, -⟩ <;> exact Sum.inl_ne_inr h.symm
  calc #G.edgeFinset + #H.edgeFinset
      = #(G.edgeFinset.image (Sym2.map Sum.inl) ∪ H.edgeFinset.image (Sym2.map Sum.inr)) := by
        rw [card_union_of_disjoint hdisj,
          card_image_of_injective _ (Sym2.map.injective Sum.inl_injective),
          card_image_of_injective _ (Sym2.map.injective Sum.inr_injective)]
    _ ≤ _ := card_le_card hsub

-- Superadditivity: the disjoint union of two `C₄`-free graphs is `C₄`-free.
theorem f_superadd (a b : ℕ) : f a + f b ≤ f (a + b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [f_zero]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [f_zero]
  obtain ⟨G, iG, hG, hGe⟩ := exists_graph a ha
  obtain ⟨H, iH, hH, hHe⟩ := exists_graph b hb
  let e : Fin a ⊕ Fin b ↪ Fin (a + b) := finSumFinEquiv.toEmbedding
  have hfree : NoTwoCommonNeighbours ((G ⊕g H).map e) := noTwo_map e (noTwo_sum hG hH)
  have h1 : #((G ⊕g H).map e).edgeFinset = #(G ⊕g H).edgeFinset := card_edgeFinset_map e _
  have h2 := card_edgeFinset_sum_ge G H
  have h3 := le_f_of_noTwoCommonNeighbours (G := (G ⊕g H).map e) (by rw [nMin_eq]; omega) hfree
  omega

theorem exists_min_degree {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    ∃ w, G.degree w ≤ 2 * #G.edgeFinset / (n + 1) := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have h1 : ∑ w : Fin (n + 1), (2 * #G.edgeFinset / (n + 1) + 1) ≤ ∑ w, G.degree w :=
    sum_le_sum (fun w _ => hcon w)
  rw [sum_degrees_eq_twice_card_edges, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact absurd (lt_of_lt_of_le (Nat.lt_mul_div_succ (2 * #G.edgeFinset) (Nat.succ_pos n)) h1)
    (lt_irrefl _)

-- `m ↦ m - ⌊2m/k⌋` is monotone for `k ≥ 2`.
theorem g_mono {m m' k : ℕ} (h : m ≤ m') (hk : 2 ≤ k) : m - 2 * m / k ≤ m' - 2 * m' / k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk0 : 0 < k := by omega
  have key : 2 * (m + d) / k ≤ 2 * m / k + d := by
    rw [Nat.div_le_iff_le_mul_add_pred hk0]
    have h1 := Nat.div_add_mod (2 * m) k
    have h2 := Nat.mod_lt (2 * m) hk0
    have h3 : 2 * d ≤ k * d := Nat.mul_le_mul_right d hk
    have h4 : k * (2 * m / k + d) = k * (2 * m / k) + k * d := Nat.mul_add _ _ _
    rw [h4]
    generalize 2 * m / k = Q at *
    generalize k * Q = A at *
    generalize k * d = B at *
    omega
  omega

-- Deleting a vertex of minimum degree from an extremal graph on `n + 1` vertices.
theorem f_del (n : ℕ) (hn : 1 ≤ n) : f (n + 1) - 2 * f (n + 1) / (n + 1) ≤ f n := by
  obtain ⟨G, iG, hG, hGe⟩ := exists_graph (n + 1) (by omega)
  obtain ⟨w, hw⟩ := exists_min_degree G
  let e : Fin n ↪ Fin (n + 1) := Fin.succAboveEmb w
  let G' : SimpleGraph (Fin n) := G.comap e
  have hfree : NoTwoCommonNeighbours G' := by
    intro x y u z hxy huz hxu hyu hxz hyz
    rw [comap_adj] at hxu hyu hxz hyz
    exact hG _ _ _ _ (fun h => hxy (e.injective h)) (fun h => huz (e.injective h)) hxu hyu hxz hyz
  have hcount : #G.edgeFinset ≤ #G'.edgeFinset + G.degree w := by
    have hsub : G.edgeFinset ⊆ G'.edgeFinset.image (Sym2.map e) ∪ G.incidenceFinset w := by
      intro s hs
      rw [mem_union, mem_image, mem_incidenceFinset]
      revert hs
      refine Sym2.ind (fun x y hs => ?_) s
      rw [mem_edgeFinset, mem_edgeSet] at hs
      by_cases hxw : x = w
      · right; subst hxw; exact ⟨hs, Sym2.mem_mk_left _ _⟩
      by_cases hyw : y = w
      · right; subst hyw; exact ⟨hs, Sym2.mem_mk_right _ _⟩
      left
      obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq hxw
      obtain ⟨y', hy'⟩ := Fin.exists_succAbove_eq hyw
      refine ⟨s(x', y'), ?_, by simp [e, hx', hy']⟩
      rw [mem_edgeFinset, mem_edgeSet, comap_adj]
      simpa [e, hx', hy'] using hs
    calc #G.edgeFinset ≤ #(G'.edgeFinset.image (Sym2.map e) ∪ G.incidenceFinset w) :=
          card_le_card hsub
      _ ≤ #(G'.edgeFinset.image (Sym2.map e)) + #(G.incidenceFinset w) := card_union_le _ _
      _ ≤ #G'.edgeFinset + G.degree w := by
          rw [card_incidenceFinset_eq_degree]; exact Nat.add_le_add_right card_image_le _
  have h3 := le_f_of_noTwoCommonNeighbours (G := G') hn hfree
  have hmono := g_mono hGe (show 2 ≤ n + 1 by omega)
  generalize 2 * f (n + 1) / (n + 1) = A at *
  generalize 2 * #G.edgeFinset / (n + 1) = B at *
  omega

/-! ### Correctness of the primality tests -/

theorem prime_of_isPrimeB {p : ℕ} (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'] at h
  obtain ⟨h2, hall⟩ := h
  rw [Nat.prime_def_lt']
  refine ⟨h2, fun m hm2 hmp hdvd => ?_⟩
  exact hall m ⟨m - 2, by omega, by omega⟩ (Nat.dvd_iff_mod_eq_zero.1 hdvd)

theorem pow_of_isPowOf {p : ℕ} :
    ∀ fuel q, isPowOf p fuel q = true → ∃ k, q = p ^ k := by
  intro fuel
  induction fuel with
  | zero => intro q h; simp [isPowOf] at h
  | succ fuel ih =>
    intro q h
    simp only [isPowOf, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | ⟨hmod, hrec⟩
    · exact ⟨0, by simp⟩
    · obtain ⟨k, hk⟩ := ih _ hrec
      refine ⟨k + 1, ?_⟩
      have hdvd : p ∣ q := Nat.dvd_of_mod_eq_zero hmod
      rw [pow_succ, ← hk, Nat.div_mul_cancel hdvd]

theorem primePow_of_isPrimePowB {q : ℕ} (h : isPrimePowB q = true) :
    ∃ p k, p.Prime ∧ k ≠ 0 ∧ q = p ^ k := by
  simp only [isPrimePowB, List.any_eq_true, List.mem_range', Bool.and_eq_true] at h
  obtain ⟨p, ⟨i, hi, rfl⟩, hprime, hpow⟩ := h
  have hp := prime_of_isPrimeB hprime
  obtain ⟨k, hk⟩ := pow_of_isPowOf _ _ hpow
  refine ⟨2 + 1 * i, k, hp, ?_, hk⟩
  rintro rfl
  rw [pow_zero] at hk
  omega

/-! ### Validity of the record -/

theorem E_le {q : ℕ} (hq : isPrimePowB q = true) : E q ≤ f (N q) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := primePow_of_isPrimePowB hq
  exact er_primePow hp hk

theorem delChain_le : ∀ (j t m : ℕ), 1 ≤ t - j → m ≤ f t → delChain j t m ≤ f (t - j) := by
  intro j
  induction j with
  | zero => intro t m _ h; simpa [delChain] using h
  | succ j ih =>
    intro t m hjt hm
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [delChain, Nat.add_sub_cancel, Nat.add_sub_add_right]
    have h1 : m - 2 * m / (s + 1) ≤ f s := le_trans (g_mono hm (by omega)) (f_del s (by omega))
    exact ih s _ (by omega) h1

theorem delVal_le {q n : ℕ} (hn : 1 ≤ n) (hq : isPrimePowB q = true) : delVal q n ≤ f n := by
  unfold delVal
  split_ifs with h
  · have := delChain_le (N q - n) (N q) (E q) (by omega) (E_le hq)
    rwa [Nat.sub_sub_self h] at this
  · exact Nat.zero_le _

theorem delLoop_le {n : ℕ} (hn : 1 ≤ n) : ∀ fuel q, delLoop n fuel q ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro q; simp [delLoop]
  | succ fuel ih =>
    intro q
    simp only [delLoop]
    by_cases h1 : q * q ≤ 2 * n
    · rw [if_pos h1]
      refine max_le ?_ (ih (q + 1))
      by_cases h2 : isPrimePowB q = true
      · rw [if_pos h2]; exact delVal_le hn h2
      · rw [if_neg h2]; exact Nat.zero_le _
    · rw [if_neg h1]; exact Nat.zero_le _

theorem delBest_le (n : ℕ) : delBest n ≤ f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [delBest, delLoop]
  · exact delLoop_le hn n 2

theorem small_le (r : ℕ) : small r ≤ f r :=
  max_le (SqueezeBench.ExC4.Lower.V005.valid r) (delBest_le r)

theorem blocks_le {q : ℕ} (hq : E q ≤ f (N q)) : ∀ k, k * E q ≤ f (N q * k) := by
  intro k
  induction k with
  | zero => simp [f_zero]
  | succ k ih =>
    calc (k + 1) * E q = k * E q + E q := by ring
      _ ≤ f (N q * k) + f (N q) := Nat.add_le_add ih hq
      _ ≤ f (N q * k + N q) := f_superadd _ _
      _ = f (N q * (k + 1)) := by ring_nf

theorem blockVal_le {q n : ℕ} (hq : isPrimePowB q = true) : blockVal q n ≤ f n := by
  unfold blockVal
  split_ifs with h
  · have h1 := blocks_le (E_le hq) (n / N q)
    have h2 := small_le (n % N q)
    have h3 := f_superadd (N q * (n / N q)) (n % N q)
    rw [Nat.div_add_mod] at h3
    omega
  · exact Nat.zero_le _

theorem blockLoop_le (n : ℕ) : ∀ fuel q, blockLoop n fuel q ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro q; simp [blockLoop]
  | succ fuel ih =>
    intro q
    simp only [blockLoop]
    by_cases h1 : q * q ≤ n
    · rw [if_pos h1]
      refine max_le ?_ (ih (q + 1))
      by_cases h2 : isPrimePowB q = true
      · rw [if_pos h2]; exact blockVal_le h2
      · rw [if_neg h2]; exact Nat.zero_le _
    · rw [if_neg h1]; exact Nat.zero_le _

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f v :=
  fun n => max_le (blockLoop_le n n 2) (delBest_le n)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExC4.Lower.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V005.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V005.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 133) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Lower.V006
