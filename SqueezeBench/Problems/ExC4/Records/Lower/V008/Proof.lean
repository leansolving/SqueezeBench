import SqueezeBench.Problems.ExC4.Records.Lower.V008.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V007.Proof

/-! Record V008 for ExC4, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V008.lean`. -/

namespace SqueezeBench.ExC4.Lower.V008

open Finset SimpleGraph SqueezeBench.ExC4 SqueezeBench.ExC4.Lower.V006

/-! ### The sub-polarity graph: `c` columns of `ER_q`, as an induced subgraph -/

section SubEmb
variable (F : Type) {c : ℕ} (m : Fin c ↪ F)

-- The sub-polarity graph on `c` columns of `ER F`: affine points `(i, d)` of the columns
-- `m i`, their points at infinity `some i`, and `none`.
abbrev SV := (Fin c × F) ⊕ Option (Fin c)

def emb : SV F (c := c) → ERV F
  | Sum.inl (i, d) => Sum.inl (m i, d)
  | Sum.inr (some i) => Sum.inr (some (m i))
  | Sum.inr none => Sum.inr none

theorem emb_injective : Function.Injective (emb F m) := by
  rintro (⟨i, d⟩ | (_ | i)) (⟨i', d'⟩ | (_ | i')) h <;>
    simp only [emb, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Option.some.injEq,
      reduceCtorEq] at h
  · obtain ⟨h1, h2⟩ := h
    rw [m.injective h1, h2]
  · rfl
  · rw [m.injective h]

end SubEmb

section SubDef
variable (F : Type) [Field F] {c : ℕ} (m : Fin c ↪ F)

def subER : SimpleGraph (SV F (c := c)) := (ER F).comap (emb F m)

theorem subER_free : NoTwoCommonNeighbours (subER F m) := by
  intro x y u v hxy huv hxu hyu hxv hyv
  simp only [subER, comap_adj] at hxu hyu hxv hyv
  exact ER_free F _ _ _ _ (fun h => hxy (emb_injective F m h))
    (fun h => huv (emb_injective F m h)) hxu hyu hxv hyv

theorem sub_adj_inl_inl {i i' : Fin c} {d d' : F} :
    (subER F m).Adj (Sum.inl (i, d)) (Sum.inl (i', d')) ↔
      (m i, d) ≠ (m i', d') ∧ m i * m i' = d + d' := Iff.rfl
theorem sub_adj_inl_some {i i' : Fin c} {d : F} :
    (subER F m).Adj (Sum.inl (i, d)) (Sum.inr (some i')) ↔ m i = m i' := Iff.rfl
theorem sub_adj_some_inl {i i' : Fin c} {d : F} :
    (subER F m).Adj (Sum.inr (some i)) (Sum.inl (i', d)) ↔ m i' = m i := Iff.rfl
theorem sub_adj_some_none {i : Fin c} : (subER F m).Adj (Sum.inr (some i)) (Sum.inr none) := trivial
theorem sub_adj_none_some {i : Fin c} : (subER F m).Adj (Sum.inr none) (Sum.inr (some i)) := trivial

end SubDef

theorem SV_card (F : Type) [Fintype F] (c : ℕ) :
    Fintype.card (SV F (c := c)) = c * Fintype.card F + c + 1 := by
  simp only [SV, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  ring

section SubCount
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] {c : ℕ} (m : Fin c ↪ F)

instance : DecidableRel (subER F m).Adj :=
  fun u v => inferInstanceAs (Decidable ((ER F).Adj (emb F m u) (emb F m v)))

theorem sdeg_none : c ≤ (subER F m).degree (Sum.inr none) := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : (univ : Finset (Fin c)).image (fun i => (Sum.inr (some i) : SV F (c := c)))
      ⊆ (subER F m).neighborFinset (Sum.inr none) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [mem_neighborFinset]
    exact sub_adj_none_some F m
  have hcard : #((univ : Finset (Fin c)).image (fun i => (Sum.inr (some i) : SV F (c := c)))) = c := by
    rw [card_image_of_injective _ (fun x y h => by simpa using h), card_univ, Fintype.card_fin]
  calc c = _ := hcard.symm
    _ ≤ _ := card_le_card hsub

theorem sdeg_some (i : Fin c) : Fintype.card F + 1 ≤ (subER F m).degree (Sum.inr (some i)) := by
  rw [← card_neighborFinset_eq_degree]
  set T := (univ : Finset F).image (fun d => (Sum.inl (i, d) : SV F (c := c))) with hT
  have hsub : T ∪ {Sum.inr none} ⊆ (subER F m).neighborFinset (Sum.inr (some i)) := by
    intro x hx
    rw [mem_union, mem_singleton, hT, mem_image] at hx
    rw [mem_neighborFinset]
    rcases hx with ⟨d, -, rfl⟩ | rfl
    · exact (sub_adj_some_inl F m).2 rfl
    · exact sub_adj_some_none F m
  have hdisj : Disjoint T {Sum.inr none} := by
    rw [disjoint_singleton_right, hT, mem_image]
    rintro ⟨d, -, h⟩
    exact Sum.inl_ne_inr h
  have hcard : #T = Fintype.card F := by
    rw [hT, card_image_of_injective _ (fun x y h => by simpa using h), card_univ]
  calc Fintype.card F + 1 = #(T ∪ {Sum.inr none}) := by
        rw [card_union_of_disjoint hdisj, hcard, card_singleton]
    _ ≤ _ := card_le_card hsub

theorem sdeg_inl (i : Fin c) (d : F) :
    c + 1 ≤ (subER F m).degree (Sum.inl (i, d)) + (if m i * m i = d + d then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree]
  set S := (univ : Finset (Fin c)).image
    (fun i' => (Sum.inl (i', m i * m i' - d) : SV F (c := c))) with hS
  have hSc : #S = c := by
    rw [hS, card_image_of_injective _ (fun x y h => (Prod.mk.inj (Sum.inl.inj h)).1), card_univ,
      Fintype.card_fin]
  have hmem : Sum.inl (i, d) ∈ S ↔ m i * m i = d + d := by
    rw [hS, mem_image]
    constructor
    · rintro ⟨i', -, h⟩
      obtain ⟨rfl, h2⟩ := Prod.mk.inj (Sum.inl.inj h)
      exact sub_eq_iff_eq_add.1 h2
    · intro h
      exact ⟨i, mem_univ _, by rw [h, add_sub_cancel_right]⟩
  have hsub : (S.erase (Sum.inl (i, d))) ∪ {Sum.inr (some i)}
      ⊆ (subER F m).neighborFinset (Sum.inl (i, d)) := by
    intro x hx
    rw [mem_union, mem_singleton, mem_erase, hS, mem_image] at hx
    rw [mem_neighborFinset]
    rcases hx with ⟨hne, i', -, rfl⟩ | rfl
    · refine ⟨fun h => hne ?_, by rw [add_sub_cancel]⟩
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have hi := m.injective h1
      subst hi
      rw [← h2]
    · exact (sub_adj_inl_some F m).2 rfl
  have hdisj : Disjoint (S.erase (Sum.inl (i, d))) {Sum.inr (some i)} := by
    rw [disjoint_singleton_right, mem_erase, hS, mem_image]
    rintro ⟨-, i', -, h⟩
    exact Sum.inl_ne_inr h
  have hle := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_singleton, card_erase_eq_ite, hSc] at hle
  have hpos : 0 < c := i.pos
  by_cases hl : m i * m i = d + d
  · rw [if_pos (hmem.2 hl)] at hle
    rw [if_pos hl]
    omega
  · rw [if_neg (fun h => hl (hmem.1 h))] at hle
    rw [if_neg hl]
    omega

theorem scard_loops_le (hm : ∀ i, m i ≠ 0) :
    #((univ : Finset (Fin c × F)).filter (fun x => m x.1 * m x.1 = x.2 + x.2)) ≤ c := by
  calc _ ≤ #(univ : Finset (Fin c)) := card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_
    _ = c := by rw [card_univ, Fintype.card_fin]
  intro x hx y hy hxy
  simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx hy
  refine Prod.ext hxy ?_
  by_cases h2 : (2 : F) = 0
  · exfalso
    apply hm x.1
    have : m x.1 * m x.1 = 0 := by rw [hx, ← two_mul, h2, zero_mul]
    exact mul_self_eq_zero.1 this
  · have : (2 : F) * x.2 = 2 * y.2 := by rw [two_mul, two_mul, ← hx, ← hy, hxy]
    exact mul_left_cancel₀ h2 this

theorem subER_edges (hm : ∀ i, m i ≠ 0) :
    c * c * Fintype.card F + 2 * c * Fintype.card F + c ≤ 2 * #(subER F m).edgeFinset := by
  rw [← sum_degrees_eq_twice_card_edges, Fintype.sum_sum_type, Fintype.sum_option]
  have hsum1 : ∑ x : Fin c × F, (c + 1) ≤
      ∑ x : Fin c × F, ((subER F m).degree (Sum.inl x) +
        (if m x.1 * m x.1 = x.2 + x.2 then 1 else 0)) :=
    sum_le_sum (fun x _ => sdeg_inl F m x.1 x.2)
  rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, sum_add_distrib,
    sum_boole, Nat.cast_id] at hsum1
  have hL := scard_loops_le F m hm
  have hsum2 : ∑ i : Fin c, (Fintype.card F + 1) ≤
      ∑ i : Fin c, (subER F m).degree (Sum.inr (some i)) :=
    sum_le_sum (fun i _ => sdeg_some F m i)
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum2
  have h3 := sdeg_none F m
  nlinarith [hsum1, hL, hsum2, h3]

end SubCount

theorem sub_bound (F : Type) [Field F] [Fintype F] [DecidableEq F] {c : ℕ} (m : Fin c ↪ F)
    (hm : ∀ i, m i ≠ 0) :
    (c * c * Fintype.card F + 2 * c * Fintype.card F + c + 1) / 2 ≤
      f (c * Fintype.card F + c + 1) := by
  let e := Fintype.equivFin (SV F (c := c))
  let G : SimpleGraph (Fin (Fintype.card (SV F (c := c)))) := (subER F m).map e.toEmbedding
  have hfree : NoTwoCommonNeighbours G := noTwo_map _ (subER_free F m)
  have hle : #G.edgeFinset ≤ f (Fintype.card (SV F (c := c))) :=
    le_f_of_noTwoCommonNeighbours (by rw [SV_card, nMin_eq]; omega) hfree
  have hle' : #G.edgeFinset ≤ f (c * Fintype.card F + c + 1) := by
    rw [← SV_card F c]; exact hle
  have hG : #G.edgeFinset = #(subER F m).edgeFinset := card_edgeFinset_map _ _
  have h2 := subER_edges F m hm
  generalize c * c * Fintype.card F + 2 * c * Fintype.card F + c = P at *
  omega

-- `c` distinct nonzero elements exist in a field of order `q` when `c + 1 ≤ q`.
theorem sub_primePow {p k c : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hc : c + 1 ≤ p ^ k) :
    (c * c * p ^ k + 2 * c * p ^ k + c + 1) / 2 ≤ f (c * p ^ k + c + 1) := by
  haveI := Fact.mk hp
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField p k) := Classical.decEq _
  have hq : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
  have hcard : Fintype.card {x : GaloisField p k // x ∈ (univ : Finset (GaloisField p k)).erase 0}
      = p ^ k - 1 := by
    rw [Fintype.card_coe, card_erase_of_mem (mem_univ _), card_univ, hq]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin c) (β := {x : GaloisField p k // x ∈ (univ : Finset (GaloisField p k)).erase 0})
    (by rw [Fintype.card_fin, hcard]; omega)
  let m : Fin c ↪ GaloisField p k := e.trans (Function.Embedding.subtype _)
  have hm : ∀ i, m i ≠ 0 := fun i => (mem_erase.1 (e i).2).1
  have := sub_bound (GaloisField p k) m hm
  rwa [hq] at this


/-! ### Validity of the record -/

theorem colVal_le {q c : ℕ} (hq : isPrimePowB q = true) (hc : c + 1 ≤ q) :
    colVal q c ≤ f (colN q c) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := primePow_of_isPrimePowB hq
  exact sub_primePow hp hk hc

theorem colDel_le {q n : ℕ} (hn : 1 ≤ n) (hq : isPrimePowB q = true) : colDel q n ≤ f n := by
  unfold colDel
  split_ifs with h
  · have := delChain_le (colN q ((n + q - 1) / (q + 1) ) - n) (colN q ((n + q - 1) / (q + 1)))
      (colVal q ((n + q - 1) / (q + 1))) (by omega) (colVal_le hq h.1)
    rwa [Nat.sub_sub_self h.2] at this
  · exact Nat.zero_le _

theorem colLoop_le {n : ℕ} (hn : 1 ≤ n) : ∀ fuel q, colLoop n fuel q ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro q; simp [colLoop]
  | succ fuel ih =>
    intro q
    simp only [colLoop]
    by_cases h1 : q * q ≤ 2 * n
    · rw [if_pos h1]
      refine max_le ?_ (ih (q + 1))
      by_cases h2 : isPrimePowB q = true
      · rw [if_pos h2]; exact colDel_le hn h2
      · rw [if_neg h2]; exact Nat.zero_le _
    · rw [if_neg h1]; exact Nat.zero_le _

theorem colBest_le (n : ℕ) : colBest n ≤ f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [colBest, colLoop]
  · exact colLoop_le hn n 2

theorem small_le (r : ℕ) : small r ≤ f r :=
  max_le (SqueezeBench.ExC4.Lower.V007.valid r) (colBest_le r)

theorem small_zero : small 0 = 0 := by decide +kernel

theorem blockVal_le {q n : ℕ} (hq : isPrimePowB q = true) : blockVal q n ≤ f n := by
  unfold blockVal
  split_ifs with h hr
  · have hk : 1 ≤ n / N q := Nat.div_pos h (by simp [N])
    have h1 := SqueezeBench.ExC4.Lower.V007.blocks_bridge_le (E_le hq) (n / N q) hk
    have h2 := Nat.div_add_mod n (N q)
    rw [hr, Nat.add_zero] at h2
    rw [h2] at h1
    rw [hr, small_zero]
    omega
  · have hk : 1 ≤ n / N q := Nat.div_pos h (by simp [N])
    have h1 := SqueezeBench.ExC4.Lower.V007.blocks_bridge_le (E_le hq) (n / N q) hk
    have h2 := small_le (n % N q)
    have h3 := SqueezeBench.ExC4.Lower.V007.f_bridge (N q * (n / N q)) (n % N q)
      (Nat.mul_pos (by simp [N]) hk) (by omega)
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
  SqueezeBench.pin_lowerBoundHolds fun n _ => max_le (colBest_le n) (blockLoop_le n n 2)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExC4.Lower.V007.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V007.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V007.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 109) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Lower.V008
