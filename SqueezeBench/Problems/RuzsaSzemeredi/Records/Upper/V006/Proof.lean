import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V006.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V005.Proof

/-! Record V006 for RuzsaSzemeredi, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V006.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V006

open Finset SimpleGraph

-- The triangles through a vertex (V002, V004, V005). Public, so that later versions can reuse it.
def trianglesAt {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (v : Fin m) :
    Finset (Finset (Fin m)) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- A triangle through `v` meets the neighbourhood of `v` in exactly its other two vertices (V002).
theorem filter_neighbor_eq {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {v : Fin m} {t : Finset (Fin m)} (ht : G.IsNClique 3 t) (hv : v ∈ t) :
    (G.neighborFinset v).filter (fun u => u ∈ t) = t.erase v := by
  ext u
  simp only [mem_filter, mem_neighborFinset, mem_erase]
  constructor
  · rintro ⟨huv, hut⟩
    exact ⟨(G.ne_of_adj huv).symm, hut⟩
  · rintro ⟨hne, hut⟩
    exact ⟨ht.1 hv hut (Ne.symm hne), hut⟩

-- Two triangles through the same edge `vu` coincide, so `2 · t_v ≤ deg v` (V002).
theorem card_trianglesAt_mul_le {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
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

-- The converse count: `deg v ≤ 2 · t_v` (V004).
theorem degree_le_card_trianglesAt_mul {m : ℕ} (G : SimpleGraph (Fin m))
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

-- So every degree is exactly twice the number of triangles at the vertex (V004).
theorem degree_eq {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (v : Fin m) : G.degree v = 2 * #(trianglesAt G v) := by
  have h1 := card_trianglesAt_mul_le G hG.edgeDisjointTriangles v
  have h2 := degree_le_card_trianglesAt_mul G hG v
  omega

-- Adjacent vertices share at most one neighbour (V003, V004).
theorem card_inter_neighborFinset_le {m : ℕ} {G : SimpleGraph (Fin m)}
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

-- The three neighbourhoods of a triangle cover at most `m` vertices and pairwise meet in single
-- vertices, so the three degrees add up to at most `m + 3` (V005).
theorem degree_sum_triangle_le {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.EdgeDisjointTriangles) {t : Finset (Fin m)} (ht : G.IsNClique 3 t) :
    ∑ v ∈ t, G.degree v ≤ m + 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp ht
  have hnab := G.ne_of_adj hab
  have hnac := G.ne_of_adj hac
  have hnbc := G.ne_of_adj hbc
  rw [Finset.sum_insert (by simp [hnab, hnac]), Finset.sum_insert (by simp [hnbc]),
    Finset.sum_singleton]
  have h1 := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  have h2 := Finset.card_union_add_card_inter
    (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset c)
  have h3 := card_inter_neighborFinset_le hG hab
  have h4 : #((G.neighborFinset a ∪ G.neighborFinset b) ∩ G.neighborFinset c) ≤ 2 := by
    have hdist : (G.neighborFinset a ∪ G.neighborFinset b) ∩ G.neighborFinset c
        = (G.neighborFinset a ∩ G.neighborFinset c)
          ∪ (G.neighborFinset b ∩ G.neighborFinset c) := by
      ext x
      simp only [mem_inter, mem_union]
      tauto
    have h5 := card_inter_neighborFinset_le hG hac
    have h6 := card_inter_neighborFinset_le hG hbc
    have := Finset.card_union_le
      (G.neighborFinset a ∩ G.neighborFinset c) (G.neighborFinset b ∩ G.neighborFinset c)
    rw [hdist]
    omega
  have h7 : #(G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset c) ≤ m := by
    simpa using Finset.card_le_univ
      (G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset c)
  have hda : #(G.neighborFinset a) = G.degree a := rfl
  have hdb : #(G.neighborFinset b) = G.degree b := rfl
  have hdc : #(G.neighborFinset c) = G.degree c := rfl
  omega

-- New in V006: the three degrees of a triangle are even, so their sum is even, and for even `m`
-- the bound `m + 3` sharpens to `m + 2`. Uniformly: the sum is at most `m + 2 + m % 2`.
theorem degree_sum_triangle_le' {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) {t : Finset (Fin m)} (ht : G.IsNClique 3 t) :
    ∑ v ∈ t, G.degree v ≤ m + 2 + m % 2 := by
  have h1 := degree_sum_triangle_le hG.edgeDisjointTriangles ht
  have h2 : ∑ v ∈ t, G.degree v = 2 * ∑ v ∈ t, #(trianglesAt G v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => degree_eq G hG v)
  omega

-- Double counting triangle-vertex incidences, with an arbitrary weight on the vertex (V005).
theorem sum_swap {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (F : Fin m → ℕ) :
    ∑ t ∈ G.cliqueFinset 3, ∑ v ∈ t, F v = ∑ v : Fin m, #(trianglesAt G v) * F v := by
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset (Fin m)))
    (s' := fun v => trianglesAt G v) (f := fun (_ : Finset (Fin m)) (v : Fin m) => F v)
    (fun x y => by simp [trianglesAt])]
  exact Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_const, smul_eq_mul])

-- Every triangle has three vertices, so the triangle counts add up to `3T` (V005).
theorem sum_card_trianglesAt {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    ∑ v : Fin m, #(trianglesAt G v) = 3 * #(G.cliqueFinset 3) := by
  have h := sum_swap G (fun _ => 1)
  simp only [mul_one] at h
  rw [← h, Finset.sum_congr rfl (fun t ht => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  exact (mem_cliqueFinset_iff.mp ht).2

-- The incidences weighted by the degree: `2 · Σ t_v² ≤ T · (m + 2 + m % 2)`.
theorem two_mul_sum_sq_le {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) :
    2 * ∑ v : Fin m, #(trianglesAt G v) ^ 2 ≤ #(G.cliqueFinset 3) * (m + 2 + m % 2) := by
  have hswap := sum_swap G (fun v => G.degree v)
  have hbound : ∑ t ∈ G.cliqueFinset 3, ∑ v ∈ t, G.degree v
      ≤ #(G.cliqueFinset 3) * (m + 2 + m % 2) := by
    calc ∑ t ∈ G.cliqueFinset 3, ∑ v ∈ t, G.degree v
        ≤ ∑ _t ∈ G.cliqueFinset 3, (m + 2 + m % 2) :=
          Finset.sum_le_sum (fun t ht =>
            degree_sum_triangle_le' hG (mem_cliqueFinset_iff.mp ht))
      _ = #(G.cliqueFinset 3) * (m + 2 + m % 2) := by rw [Finset.sum_const, smul_eq_mul]
  have hrw : ∑ v : Fin m, #(trianglesAt G v) * G.degree v
      = 2 * ∑ v : Fin m, #(trianglesAt G v) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [degree_eq G hG v]; ring)
  rw [hswap, hrw] at hbound
  exact hbound

-- The main estimate: `18 · T ≤ m(m + 2 + m % 2)` for a locally linear graph on `m` vertices.
theorem eighteen_mul_card_le {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : 18 * #(G.cliqueFinset 3) ≤ m * (m + 2 + m % 2) := by
  set T := #(G.cliqueFinset 3) with hT
  set S := ∑ v : Fin m, #(trianglesAt G v) with hS
  set Q := ∑ v : Fin m, #(trianglesAt G v) ^ 2 with hQ
  have hsum1 : S = 3 * T := sum_card_trianglesAt G
  have hsum2 : 2 * Q ≤ T * (m + 2 + m % 2) := two_mul_sum_sq_le G hG
  -- Cauchy-Schwarz on the triangle counts
  have hcs : S ^ 2 ≤ m * Q := by
    rw [hS, hQ]
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun v => #(trianglesAt G v))
  rcases Nat.eq_zero_or_pos T with hz | hz
  · simp [hz]
  · have h9 : 9 * (T * T) ≤ m * Q := by
      rw [hsum1] at hcs
      nlinarith [hcs]
    have hmain : 18 * T * T ≤ m * (m + 2 + m % 2) * T := by
      nlinarith [h9, hsum2, Nat.zero_le m]
    exact Nat.le_of_mul_le_mul_right hmain hz

theorem eighteen_mul_le (n : ℕ) : 18 * ruzsaSzemerediNumberNat n ≤ n * (n + 2 + n % 2) := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  exact eighteen_mul_card_le G hLL

-- The triangle counts of an extremal graph, for later versions: they add up to `3T` and their
-- squares satisfy the weighted incidence bound.
theorem exists_counts (n : ℕ) : ∃ t : Fin n → ℕ,
    ∑ v, t v = 3 * ruzsaSzemerediNumberNat n ∧
    2 * ∑ v, t v ^ 2 ≤ ruzsaSzemerediNumberNat n * (n + 2 + n % 2) := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  exact ⟨fun v => #(trianglesAt G v), sum_card_trianglesAt G, two_mul_sum_sq_le G hLL⟩

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · rw [SqueezeBench.RuzsaSzemeredi.f_of_le h]
    rw [show record n = n * (n + 2 + n % 2) / 18 from rfl]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := eighteen_mul_le n
    omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V005.record record := by
  intro n
  show n * (n + 2 + n % 2) / 18 ≤ n * (n + 3) / 18
  exact Nat.div_le_div_right (Nat.mul_le_mul le_rfl (by omega))

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V005.record record :=
  ⟨10, by decide, by decide⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V006
