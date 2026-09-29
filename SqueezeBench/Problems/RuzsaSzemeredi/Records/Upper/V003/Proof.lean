import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V003.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V002.Proof

/-! Record V003 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V003.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V003

open Finset SimpleGraph

-- Two triangles on the same edge coincide, so adjacent vertices share at most one neighbour.
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

-- Hence `|N(u)| + |N(v)| = |N(u) ∪ N(v)| + |N(u) ∩ N(v)| ≤ m + 1` along every edge.
private theorem degree_add_degree_le {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.EdgeDisjointTriangles) {u v : Fin m} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ m + 1 := by
  have h := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h1 : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ m := by
    simpa using Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
  have h2 := card_inter_neighborFinset_le hG huv
  have hdu : #(G.neighborFinset u) = G.degree u := rfl
  have hdv : #(G.neighborFinset v) = G.degree v := rfl
  omega

-- `(c - d)² + (c - d) ≥ 0`, written without subtraction.
private theorem key_arith (c d : ℕ) : 2 * c * d + d ≤ c * c + d * d + c := by
  rcases Nat.lt_or_ge c d with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    nlinarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith

private theorem combine {c d e m : ℕ} (hm : c + d = m)
    (h : 2 * e + d * d ≤ d * (m + 1) + c * d) : 4 * e ≤ m * (m + 1) := by
  subst hm
  nlinarith [key_arith c d]

-- The maximum-degree count: `4 · #edges ≤ m(m+1)`.
private theorem four_mul_card_edgeFinset_le {m : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (hG : G.EdgeDisjointTriangles) :
    4 * #G.edgeFinset ≤ m * (m + 1) := by
  have hdeg : ∑ u : Fin m, G.degree u = 2 * #G.edgeFinset :=
    G.sum_degrees_eq_twice_card_edges
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hdeg
    omega
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    have : 0 < Fintype.card (Fin m) := by simpa using hm
    exact Finset.card_pos.mp (by simpa using this)
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image Finset.univ (fun u => G.degree u) hne
  have hsub : G.neighborFinset v ⊆ Finset.univ := Finset.subset_univ _
  have hcard : #(Finset.univ \ G.neighborFinset v) + G.degree v = m := by
    have := Finset.card_sdiff_add_card_eq_card hsub
    have hd : #(G.neighborFinset v) = G.degree v := rfl
    simpa [hd] using this
  have hsum1 : (∑ u ∈ G.neighborFinset v, G.degree u) + G.degree v * G.degree v
      ≤ G.degree v * (m + 1) := by
    have key : ∑ u ∈ G.neighborFinset v, (G.degree u + G.degree v)
        ≤ ∑ _u ∈ G.neighborFinset v, (m + 1) := by
      refine Finset.sum_le_sum ?_
      intro u hu
      rw [mem_neighborFinset] at hu
      exact degree_add_degree_le hG hu.symm
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
  refine combine hcard ?_
  omega

-- Together with `3 · T ≤ #edges` this is the bound `12 · T ≤ n(n+1)`.
theorem twelve_mul_le (n : ℕ) : 12 * ruzsaSzemerediNumberNat n ≤ n * (n + 1) := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  have h1 : 3 * #(G.cliqueFinset 3) ≤ #G.edgeFinset :=
    hLL.edgeDisjointTriangles.card_edgeFinset_le
  have h2 := four_mul_card_edgeFinset_le G hLL.edgeDisjointTriangles
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  calc 12 * #(G.cliqueFinset 3) = 4 * (3 * #(G.cliqueFinset 3)) := by ring
    _ ≤ 4 * #G.edgeFinset := by omega
    _ ≤ n * (n + 1) := h2

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · rw [SqueezeBench.RuzsaSzemeredi.f_of_le h]
    rw [show record n = n * (n + 1) / 12 from rfl]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := twelve_mul_le n
    omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V002.record record := by
  intro n
  show n * (n + 1) / 12 ≤ n * ((n - 1) / 2) / 3
  rcases lt_or_ge n 7 with h | h
  · interval_cases n <;> decide
  · have hq : n ≤ 2 * ((n - 1) / 2) + 2 := by omega
    have hA : n * n ≤ n * (2 * ((n - 1) / 2) + 2) := Nat.mul_le_mul le_rfl hq
    have hB : 5 * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have h4 : n * (n + 1) ≤ 4 * (n * ((n - 1) / 2)) := by nlinarith
    calc n * (n + 1) / 12 ≤ (4 * (n * ((n - 1) / 2))) / 12 := Nat.div_le_div_right h4
      _ = n * ((n - 1) / 2) / 3 := by
          rw [show (12 : ℕ) = 4 * 3 from rfl, ← Nat.div_div_eq_div_mul,
            Nat.mul_div_cancel_left _ (by norm_num)]

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V002.record record :=
  ⟨5, by decide, by decide⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V003
