import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V002.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V001.Proof

/-! Record V002 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V002.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V002

open Finset SimpleGraph

-- The triangles through a fixed vertex, as a `Finset`.
private def trianglesAt {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (v : Fin m) :
    Finset (Finset (Fin m)) :=
  (G.cliqueFinset 3).filter (fun t => v ∈ t)

-- A triangle through `v` meets the neighbourhood of `v` in exactly its other two vertices.
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

-- Two triangles through the same edge `vu` coincide: that is edge-disjointness.
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

-- Double counting the incidences between triangles and vertices.
theorem three_mul_le (n : ℕ) : 3 * ruzsaSzemerediNumberNat n ≤ n * ((n - 1) / 2) := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  have hdeg : ∀ v : Fin n, #(trianglesAt G v) ≤ (n - 1) / 2 := by
    intro v
    have h1 := card_trianglesAt_mul_le G hLL.edgeDisjointTriangles v
    have h2 : G.degree v < Fintype.card (Fin n) := G.degree_lt_card_verts v
    rw [Fintype.card_fin] at h2
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have key := Finset.card_mul_le_card_mul (r := fun (t : Finset (Fin n)) (v : Fin n) => v ∈ t)
    (s := G.cliqueFinset 3) (t := (Finset.univ : Finset (Fin n))) (m := 3) (n := (n - 1) / 2)
    (by
      intro t ht
      rw [mem_cliqueFinset_iff] at ht
      have : (Finset.univ : Finset (Fin n)).bipartiteAbove (fun t v => v ∈ t) t = t := by
        simp [Finset.bipartiteAbove]
      rw [this, ht.2])
    (by
      intro v _
      have : (G.cliqueFinset 3).bipartiteBelow (fun t v => v ∈ t) v = trianglesAt G v := rfl
      rw [this]
      exact hdeg v)
  rw [Finset.card_univ, Fintype.card_fin] at key
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  omega

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · rw [SqueezeBench.RuzsaSzemeredi.f_of_le h]
    rw [show record n = n * ((n - 1) / 2) / 3 from rfl]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := three_mul_le n
    omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V001.record record := by
  intro n
  show n * ((n - 1) / 2) / 3 ≤ n.choose 2 / 3
  refine Nat.div_le_div_right ?_
  rw [Nat.choose_two_right]
  exact Nat.mul_div_le_mul_div_assoc n (n - 1) 2

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V001.record record :=
  ⟨6, by decide, by decide⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V002
