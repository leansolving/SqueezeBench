import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V004.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V003.Proof

/-! Record V004 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V004.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V004

open Finset SimpleGraph

-- The triangles through a vertex, as in V002.
private def trianglesAt {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (v : Fin m) :
    Finset (Finset (Fin m)) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- A triangle through `v` meets the neighbourhood of `v` in exactly its other two vertices (V002).
private theorem filter_neighbor_eq {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {v : Fin m} {t : Finset (Fin m)} (ht : G.IsNClique 3 t) (hv : v ∈ t) :
    (G.neighborFinset v).filter (fun u => u ∈ t) = t.erase v := by
  ext u
  simp only [mem_filter, mem_neighborFinset, mem_erase]
  constructor
  · rintro ⟨huv, hut⟩
    exact ⟨(G.ne_of_adj huv).symm, hut⟩
  · rintro ⟨hne, hut⟩
    exact ⟨ht.1 hv hut (Ne.symm hne), hut⟩

-- Two triangles through the same edge `vu` coincide (V002).
private theorem card_trianglesAt_mul_le {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.EdgeDisjointTriangles) (v : Fin m) :
    #(trianglesAt G v) * 2 ≤ G.degree v := by
  have := Finset.card_mul_le_card_mul (r := fun (t : Finset (Fin m)) (u : Fin m) => u ∈ t)
    (s := trianglesAt G v) (t := G.neighborFinset v) (m := 2) (n := 1)
    ?_ ?_
  · have hd : G.degree v = #(G.neighborFinset v) := rfl
    omega
  · intro t ht
    simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff] at ht
    have hcard : (t.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem ht.2, ht.1.2]
    have : (G.neighborFinset v).bipartiteAbove (fun t u => u ∈ t) t = t.erase v := by
      simpa [Finset.bipartiteAbove] using filter_neighbor_eq ht.1 ht.2
    rw [this, hcard]
  · intro u hu
    rw [Finset.card_le_one]
    intro t₁ h₁ t₂ h₂
    simp only [Finset.bipartiteBelow, mem_filter, trianglesAt, mem_cliqueFinset_iff] at h₁ h₂
    by_contra hne
    have hsub := hG (by simpa [mem_cliqueSet_iff] using h₁.1.1)
      (by simpa [mem_cliqueSet_iff] using h₂.1.1) hne
    have hvu : v ≠ u := (G.ne_of_adj (by simpa using hu))
    exact hvu (hsub ⟨h₁.1.2, h₂.1.2⟩ ⟨h₁.2, h₂.2⟩)

-- The converse count: every neighbour of `v` lies in a triangle through `v`, and each such
-- triangle absorbs two neighbours, so `deg v ≤ 2 · #(triangles at v)`.
private theorem degree_le_card_trianglesAt_mul {m : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (hG : G.LocallyLinear) (v : Fin m) :
    G.degree v ≤ #(trianglesAt G v) * 2 := by
  have := Finset.card_mul_le_card_mul (r := fun (u : Fin m) (t : Finset (Fin m)) => u ∈ t)
    (s := G.neighborFinset v) (t := trianglesAt G v) (m := 1) (n := 2)
    ?_ ?_
  · have hd : G.degree v = #(G.neighborFinset v) := rfl
    omega
  · intro u hu
    rw [mem_neighborFinset] at hu
    obtain ⟨t, ht, hvt, hut⟩ := hG.2 hu
    refine Finset.card_pos.mpr ⟨t, ?_⟩
    simp only [Finset.bipartiteAbove, mem_filter, trianglesAt, mem_cliqueFinset_iff]
    exact ⟨⟨ht, hvt⟩, hut⟩
  · intro t ht
    simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff] at ht
    have : (G.neighborFinset v).bipartiteBelow (fun (u : Fin m) (t : Finset (Fin m)) => u ∈ t) t
        = t.erase v := by
      simpa [Finset.bipartiteBelow] using filter_neighbor_eq ht.1 ht.2
    rw [this, Finset.card_erase_of_mem ht.2, ht.1.2]

-- Hence every degree is even.
private theorem degree_even {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (v : Fin m) : G.degree v % 2 = 0 := by
  have h1 := card_trianglesAt_mul_le G hG.edgeDisjointTriangles v
  have h2 := degree_le_card_trianglesAt_mul G hG v
  omega

-- Adjacent vertices share at most one neighbour (V003).
private theorem card_inter_neighborFinset_le {m : ℕ} {G : SimpleGraph (Fin m)}
    [DecidableRel G.Adj] (hG : G.EdgeDisjointTriangles) {u v : Fin m} (huv : G.Adj u v) :
    #(G.neighborFinset u ∩ G.neighborFinset v) ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  simp only [mem_inter, mem_neighborFinset] at ha hb
  have hta : G.IsNClique 3 {u, v, a} := is3Clique_triple_iff.mpr ⟨huv, ha.1, ha.2⟩
  have htb : G.IsNClique 3 {u, v, b} := is3Clique_triple_iff.mpr ⟨huv, hb.1, hb.2⟩
  have hsne : ({u, v, a} : Finset (Fin m)) ≠ {u, v, b} := by
    intro h
    have hmem : a ∈ ({u, v, b} : Finset (Fin m)) := by
      rw [← h]; simp
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact (G.ne_of_adj ha.1).symm h1
    · exact (G.ne_of_adj ha.2).symm h1
    · exact hne h1
  have hsub := hG (by simpa [mem_cliqueSet_iff] using hta)
    (by simpa [mem_cliqueSet_iff] using htb) hsne
  exact (G.ne_of_adj huv) (hsub ⟨by simp, by simp⟩ ⟨by simp, by simp⟩)

-- `deg u + deg v ≤ m + 1` along every edge (V003); even, so `≤ m` when `m` is even.
private theorem degree_add_degree_le_even {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (hm : m % 2 = 0) {u v : Fin m} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ m := by
  have h := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h1 : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ m := by
    simpa using Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
  have h2 := card_inter_neighborFinset_le hG.edgeDisjointTriangles huv
  have hdu : #(G.neighborFinset u) = G.degree u := rfl
  have hdv : #(G.neighborFinset v) = G.degree v := rfl
  have h3 := degree_even G hG u
  have h4 := degree_even G hG v
  omega

-- The maximum-degree split of V003, with the bound along an edge as a parameter.
private theorem exists_split {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (M : ℕ)
    (hM : ∀ u v : Fin m, G.Adj u v → G.degree u + G.degree v ≤ M) :
    ∃ c d, c + d = m ∧ 2 * #G.edgeFinset + d * d ≤ d * M + c * d := by
  have hdeg : ∑ u : Fin m, G.degree u = 2 * #G.edgeFinset :=
    G.sum_degrees_eq_twice_card_edges
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, 0, rfl, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hdeg
    omega
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    have : 0 < Fintype.card (Fin m) := by simpa using hm
    exact Finset.card_pos.mp (by simpa using this)
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image Finset.univ (fun u => G.degree u) hne
  have hsub : G.neighborFinset v ⊆ Finset.univ := Finset.subset_univ _
  refine ⟨#(Finset.univ \ G.neighborFinset v), G.degree v, ?_, ?_⟩
  · have := Finset.card_sdiff_add_card_eq_card hsub
    have hd : #(G.neighborFinset v) = G.degree v := rfl
    simpa [hd] using this
  have hsum1 : (∑ u ∈ G.neighborFinset v, G.degree u) + G.degree v * G.degree v
      ≤ G.degree v * M := by
    have key : ∑ u ∈ G.neighborFinset v, (G.degree u + G.degree v)
        ≤ ∑ _u ∈ G.neighborFinset v, M := by
      refine Finset.sum_le_sum ?_
      intro u hu
      rw [mem_neighborFinset] at hu
      exact hM u v hu.symm
    have hd : #(G.neighborFinset v) = G.degree v := rfl
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hd] at key
    linarith [key]
  have hsum2 : (∑ u ∈ Finset.univ \ G.neighborFinset v, G.degree u)
      ≤ #(Finset.univ \ G.neighborFinset v) * G.degree v := by
    have key : (∑ u ∈ Finset.univ \ G.neighborFinset v, G.degree u)
        ≤ ∑ _u ∈ Finset.univ \ G.neighborFinset v, G.degree v :=
      Finset.sum_le_sum (fun u _ => hv u (Finset.mem_univ u))
    simpa [Finset.sum_const, smul_eq_mul] using key
  have hsplit : (∑ u ∈ Finset.univ \ G.neighborFinset v, G.degree u)
      + (∑ u ∈ G.neighborFinset v, G.degree u) = ∑ u : Fin m, G.degree u :=
    Finset.sum_sdiff hsub
  omega

private theorem two_mul_le_add_mul (a b : ℕ) : 2 * a * b ≤ a * a + b * b := by
  rcases Nat.lt_or_ge a b with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    nlinarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith

-- With `M = m` the count closes on `(m - 2d)² ≥ 0` alone.
private theorem combine_even {c d e m : ℕ} (hm : c + d = m)
    (h : 2 * e + d * d ≤ d * m + c * d) : 4 * e ≤ m * m := by
  subst hm
  nlinarith [two_mul_le_add_mul c d]

theorem twelve_mul_le_even {n : ℕ} (hn : n % 2 = 0) :
    12 * ruzsaSzemerediNumberNat n ≤ n * n := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  have h1 : 3 * #(G.cliqueFinset 3) ≤ #G.edgeFinset :=
    hLL.edgeDisjointTriangles.card_edgeFinset_le
  obtain ⟨c, d, hcd, hsum⟩ := exists_split G n (fun u v h => degree_add_degree_le_even hLL hn h)
  have h2 : 4 * #G.edgeFinset ≤ n * n := combine_even hcd hsum
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  calc 12 * #(G.cliqueFinset 3) = 4 * (3 * #(G.cliqueFinset 3)) := by ring
    _ ≤ 4 * #G.edgeFinset := by omega
    _ ≤ n * n := h2

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · rw [SqueezeBench.RuzsaSzemeredi.f_of_le h]
    rw [show record n = n * (2 * ((n + 1) / 2)) / 12 from rfl]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · have he : 2 * ((n + 1) / 2) = n := by omega
      rw [he]
      have := twelve_mul_le_even hp
      omega
    · have he : 2 * ((n + 1) / 2) = n + 1 := by omega
      rw [he]
      have := SqueezeBench.RuzsaSzemeredi.Upper.V003.twelve_mul_le n
      omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V003.record record := by
  intro n
  show n * (2 * ((n + 1) / 2)) / 12 ≤ n * (n + 1) / 12
  exact Nat.div_le_div_right (Nat.mul_le_mul le_rfl (by omega))

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V003.record record :=
  ⟨8, by decide, by decide⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V004
