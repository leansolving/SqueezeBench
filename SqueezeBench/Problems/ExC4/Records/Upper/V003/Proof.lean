import SqueezeBench.Problems.ExC4.Records.Upper.V003.Def
import SqueezeBench.Problems.ExC4.Records.Upper.V002.Proof

/-! Record V003 for ExC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Upper/V003.lean`. -/

namespace SqueezeBench.ExC4.Upper.V003

open Finset SimpleGraph

variable {n : ℕ}

-- The ordered pairs of adjacent neighbours of `v`: the edges inside `N(v)`, both ways round.
def zset (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : Finset (Fin n × Fin n) :=
  ((G.neighborFinset v) ×ˢ (G.neighborFinset v)).filter (fun p => G.Adj p.1 p.2)

-- The neighbours of `v` that share a neighbour with `v`.
def mset (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : Finset (Fin n) :=
  (zset G v).image Prod.fst

-- The ordered pairs of distinct neighbours of `v`, together with the pairs `(v, x)` for the
-- neighbours `x` that share no neighbour with `v`.
def uset (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : Finset (Fin n × Fin n) :=
  (G.neighborFinset v).offDiag ∪ ({v} ×ˢ ((G.neighborFinset v) \ mset G v))

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem mem_zset {v : Fin n} {p : Fin n × Fin n} :
    p ∈ zset G v ↔ (G.Adj v p.1 ∧ G.Adj v p.2 ∧ G.Adj p.1 p.2) := by
  simp [zset, Finset.mem_product, and_assoc]

theorem mem_mset {v x : Fin n} :
    x ∈ mset G v ↔ ∃ y, G.Adj v x ∧ G.Adj v y ∧ G.Adj x y := by
  simp only [mset, Finset.mem_image, mem_zset]
  constructor
  · rintro ⟨p, ⟨h1, h2, h3⟩, rfl⟩; exact ⟨p.2, h1, h2, h3⟩
  · rintro ⟨y, h1, h2, h3⟩; exact ⟨(x, y), ⟨h1, h2, h3⟩, rfl⟩

theorem mset_subset (v : Fin n) : mset G v ⊆ G.neighborFinset v := by
  intro x hx
  rw [mem_mset] at hx
  obtain ⟨y, h1, -, -⟩ := hx
  simpa using h1

-- Projecting an edge inside `N(v)` to its first end is injective: two edges of `N(v)` with the
-- same first end `x` would give `v` and `x` two common neighbours.
theorem card_mset_eq (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (v : Fin n) :
    #(mset G v) = #(zset G v) := by
  refine Finset.card_image_of_injOn ?_
  intro p hp p' hp' h
  rw [Finset.mem_coe, mem_zset] at hp hp'
  obtain ⟨h1, h2, h3⟩ := hp
  obtain ⟨h1', h2', h3'⟩ := hp'
  by_cases hs : p.2 = p'.2
  · exact Prod.ext h hs
  · have h3'' : G.Adj p.1 p'.2 := by rw [h]; exact h3'
    exact (hG v p.1 p.2 p'.2 (G.ne_of_adj h1) hs h2 h3 h2' h3'').elim

-- The edge set of `N(v)` comes in swapped pairs, so it has even size.
theorem card_zset_even (v : Fin n) : ∃ t, #(zset G v) = 2 * t := by
  refine ⟨#((zset G v).filter (fun p => p.1 < p.2)), ?_⟩
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := zset G v) (p := fun p => p.1 < p.2)
  have himg : (zset G v).filter (fun p => ¬ p.1 < p.2)
      = ((zset G v).filter (fun p => p.1 < p.2)).image Prod.swap := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image, mem_zset]
    constructor
    · rintro ⟨⟨ha, hb, hc⟩, hlt⟩
      refine ⟨p.swap, ⟨⟨hb, ha, hc.symm⟩, ?_⟩, Prod.swap_swap p⟩
      exact lt_of_le_of_ne (not_lt.mp hlt) (G.ne_of_adj hc).symm
    · rintro ⟨r, ⟨⟨ha, hb, hc⟩, hlt⟩, rfl⟩
      refine ⟨⟨hb, ha, hc.symm⟩, ?_⟩
      simpa using not_lt.mpr (le_of_lt hlt)
  rw [himg, Finset.card_image_of_injective _ Prod.swap_injective] at hsplit
  omega

theorem card_mset_le (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (v : Fin n) :
    #(mset G v) ≤ 2 * (G.degree v / 2) := by
  obtain ⟨t, ht⟩ := card_zset_even G v
  have h1 : #(mset G v) = 2 * t := by rw [card_mset_eq G hG v, ht]
  have h2 : #(mset G v) ≤ G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (mset_subset G v)
  omega

theorem uset_card (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (v : Fin n) :
    #(uset G v) + #(mset G v) = G.degree v * G.degree v := by
  have hd : #(G.neighborFinset v) = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
  have hdisj : Disjoint ((G.neighborFinset v).offDiag)
      (({v} ×ˢ ((G.neighborFinset v) \ mset G v))) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_offDiag] at hp
    rw [Finset.mem_product, Finset.mem_singleton] at hp'
    have : v ∈ G.neighborFinset v := hp'.1 ▸ hp.1
    simp at this
  have hsd : #((G.neighborFinset v) \ mset G v) + #(mset G v) = G.degree v := by
    rw [Finset.card_sdiff_add_card_eq_card (mset_subset G v), hd]
  have hcard : #(uset G v)
      = (G.degree v * G.degree v - G.degree v) + #((G.neighborFinset v) \ mset G v) := by
    rw [uset, Finset.card_union_of_disjoint hdisj, Finset.offDiag_card, hd,
      Finset.card_product, Finset.card_singleton, one_mul]
  have h3 : G.degree v ≤ G.degree v * G.degree v := by
    rcases Nat.eq_zero_or_pos (G.degree v) with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  omega

-- The `uset`s are pairwise disjoint sets of ordered pairs of distinct vertices.
theorem mem_uset {v : Fin n} {p : Fin n × Fin n} :
    p ∈ uset G v ↔ ((G.Adj v p.1 ∧ G.Adj v p.2 ∧ p.1 ≠ p.2)
      ∨ (p.1 = v ∧ G.Adj v p.2 ∧ p.2 ∉ mset G v)) := by
  simp only [uset, Finset.mem_union, Finset.mem_offDiag, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, and_assoc]

theorem uset_disjoint (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {v w : Fin n}
    (hvw : v ≠ w) : Disjoint (uset G v) (uset G w) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_uset] at hp hq
  rcases hp with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;> rcases hq with ⟨ha', hb', hc'⟩ | ⟨ha', hb', hc'⟩
  · exact hG v w p.1 p.2 hvw hc ha ha' hb hb'
  · refine hc' ?_
    rw [mem_mset]
    exact ⟨v, hb', (ha' ▸ ha).symm, hb.symm⟩
  · refine hc ?_
    rw [mem_mset]
    exact ⟨w, hb, (ha ▸ ha').symm, hb'.symm⟩
  · exact hvw (ha.symm.trans ha')

theorem sum_sq_le (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) :
    ∑ v : Fin n, (G.degree v * G.degree v) ≤ n * n - n + ∑ v : Fin n, 2 * (G.degree v / 2) := by
  have hsub : (univ : Finset (Fin n)).biUnion (fun v => uset G v) ⊆ (univ : Finset (Fin n)).offDiag := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, -, hv⟩ := hp
    rw [mem_uset] at hv
    rw [Finset.mem_offDiag]
    rcases hv with ⟨-, -, hc⟩ | ⟨ha, hb, -⟩
    · exact ⟨Finset.mem_univ _, Finset.mem_univ _, hc⟩
    · exact ⟨Finset.mem_univ _, Finset.mem_univ _, by rw [ha]; exact G.ne_of_adj hb⟩
  have hcard : ∑ v : Fin n, #(uset G v) ≤ n * n - n := by
    rw [← Finset.card_biUnion (fun x _ y _ h => uset_disjoint G hG h)]
    have := Finset.card_le_card hsub
    rwa [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at this
  have hsum : ∑ v : Fin n, (#(uset G v) + #(mset G v)) = ∑ v : Fin n, (G.degree v * G.degree v) :=
    Finset.sum_congr rfl fun v _ => uset_card G hG v
  have hm : ∑ v : Fin n, #(mset G v) ≤ ∑ v : Fin n, 2 * (G.degree v / 2) :=
    Finset.sum_le_sum fun v _ => card_mset_le G hG v
  rw [Finset.sum_add_distrib] at hsum
  omega

-- The tangent line to `d ↦ d² − 2⌊d/2⌋` at an odd `q`, with slope `2q − 1`.
theorem tangent {q d : ℕ} (hq : q % 2 = 1) : 1 + 2 * q * d ≤ d * d + q * q + d % 2 := by
  rcases lt_trichotomy d q with h | rfl | h
  · obtain ⟨e, rfl⟩ : ∃ e, q = d + 1 + e := ⟨q - (d + 1), by omega⟩
    nlinarith [Nat.zero_le (d % 2)]
  · rw [hq]; nlinarith
  · obtain ⟨e, rfl⟩ : ∃ e, d = q + 1 + e := ⟨d - (q + 1), by omega⟩
    nlinarith [Nat.zero_le ((q + 1 + e) % 2)]

theorem key (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {q : ℕ} (hq : q % 2 = 1) :
    (2 * q - 1) * (2 * #G.edgeFinset) + n ≤ n * (n - 1) + n * (q * q) := by
  obtain ⟨m, hm⟩ : ∃ m, #G.edgeFinset = m := ⟨_, rfl⟩
  have hdeg : ∑ v : Fin n, G.degree v = 2 * m := by
    rw [← hm]; exact G.sum_degrees_eq_twice_card_edges
  have htan : ∑ v : Fin n, (1 + 2 * q * G.degree v)
      ≤ ∑ v : Fin n, (G.degree v * G.degree v + q * q + G.degree v % 2) :=
    Finset.sum_le_sum fun v _ => tangent hq
  have hmod : ∀ v : Fin n, G.degree v % 2 + 2 * (G.degree v / 2) = G.degree v := fun v => by omega
  have hsplit : ∑ v : Fin n, (G.degree v % 2 + 2 * (G.degree v / 2)) = 2 * m := by
    rw [← hdeg]; exact Finset.sum_congr rfl fun v _ => hmod v
  rw [Finset.sum_add_distrib] at hsplit
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, ← Finset.mul_sum, hdeg] at htan
  have hsq := sum_sq_le G hG
  have hq1 : 1 ≤ q := by omega
  have hs : 2 * q - 1 + 1 = 2 * q := by omega
  have hexp : (2 * q - 1) * (2 * m) + (2 * m) = 2 * q * (2 * m) := by
    calc (2 * q - 1) * (2 * m) + (2 * m) = ((2 * q - 1) + 1) * (2 * m) := by ring
      _ = 2 * q * (2 * m) := by rw [hs]
  have hn : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  have hnn : n * (n - 1) + n = n * n := by
    cases n with
    | zero => simp
    | succ k => simp only [Nat.succ_sub_one]; ring
  rw [hm]
  omega

theorem tangentBound_le (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {q : ℕ}
    (hq : q % 2 = 1) : #G.edgeFinset ≤ tangentBound n q := by
  have hk := key G hG hq
  have hq1 : 1 ≤ q := by omega
  have hs : 0 < 2 * q - 1 := by omega
  have hmul : (2 * #G.edgeFinset) * (2 * q - 1) ≤ n * (n - 1) + n * (q * q) - n := by
    have := Nat.mul_comm (2 * q - 1) (2 * #G.edgeFinset)
    omega
  have h1 : 2 * #G.edgeFinset ≤ (n * (n - 1) + n * (q * q) - n) / (2 * q - 1) :=
    (Nat.le_div_iff_mul_le hs).mpr hmul
  rw [tangentBound]
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)

theorem qBase_odd (n : ℕ) : qBase n % 2 = 1 := by
  rw [qBase]; omega

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f v := by
  intro n
  match n with
  | 0 =>
      have h0 : SqueezeBench.ExC4.f 0 = 0 :=
        Nat.le_zero.mp (by simpa using SqueezeBench.ExC4.f_le_choose_two 0)
      rw [h0]
      exact Nat.zero_le _
  | (k + 1) =>
      refine SqueezeBench.ExC4.f_le_of_forall_noTwoCommonNeighbours (by simp) ?_
      intro G _ hG
      refine le_min (tangentBound_le G hG (qBase_odd (k + 1))) ?_
      exact tangentBound_le G hG (by have := qBase_odd (k + 1); omega)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExC4.Upper.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V002.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V002.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 6) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Upper.V003
