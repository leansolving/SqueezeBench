import SqueezeBench.Problems.ExGirthFive.Records.Upper.V003.Def
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V002.Proof

/-! Record V003 for ExGirthFive, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Upper/V003.lean`.

V002 fed the summed degree count `∑ d(w)² ≤ n² - n` to the chord of `x ↦ x²` at `q`. Here the
*per-vertex* form of that count is used as well: for every vertex `x`, the vertices at distance
exactly two from `x` are pairwise distinct and avoid the closed neighbourhood of `x`, so
`∑_{u ~ x} d(u) ≤ n - 1`. Consequently either every degree is at most `q`, and `2m ≤ n·q`, or
some vertex has degree `q + 1` or more and then a vertex of minimum degree has degree at most
`(n-1)/(q+1)`. In the second case that vertex is pulled out of the chord sum, where it
contributes `d(2q+1) - d²` instead of `q(q+1)`, and `d ≤ (n-1)/(q+1) < q` makes this strictly
smaller. -/

namespace SqueezeBench.ExGirthFive.Upper.V003

open Finset SimpleGraph

-- The chord of `x ↦ x²` through `(L, L²)` and `(2q+1-L, …)`, used at the pulled-out vertex.
theorem chord2 (D L q : ℕ) (hL : L ≤ q) (h : D ≤ L ∨ L = q) :
    (2 * q + 1) * D ≤ D * D + L * (2 * q + 1 - L) := by
  obtain ⟨U, hUeq⟩ : ∃ U, 2 * q + 1 = L + U := ⟨2 * q + 1 - L, by omega⟩
  have hrw : 2 * q + 1 - L = U := by omega
  rw [hrw, hUeq]
  rcases h with h | h
  · have hDU : D ≤ U := by omega
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hDU
    subst ha
    subst hb
    nlinarith [Nat.zero_le (a * b)]
  · have hUq : U = q + 1 := by omega
    have hch := V002.chord D q
    rw [pow_two] at hch
    rw [h, hUq]
    calc (q + (q + 1)) * D = (2 * q + 1) * D := by ring
      _ ≤ _ := hch

-- For every vertex `x`, the neighbours of the neighbours of `x` other than `x` itself are
-- pairwise distinct and lie outside the closed neighbourhood of `x`.
theorem nbr_sum_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (h4 : SqueezeBench.ExGirthFive.NoTwoCommonNeighbours G) (x : Fin n) :
    ∑ u ∈ G.neighborFinset x, G.degree u ≤ n - 1 := by
  classical
  set S := (G.neighborFinset x).sigma (fun u => (G.neighborFinset u).erase x) with hSdef
  have hmem : ∀ p ∈ S, (fun p : (_ : Fin n) × Fin n => p.2) p ∈
      (univ.erase x) \ G.neighborFinset x := by
    rintro ⟨u, y⟩ hp
    simp only [hSdef, Finset.mem_sigma, Finset.mem_erase, mem_neighborFinset] at hp
    obtain ⟨hxu, hyx, huy⟩ := hp
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, mem_neighborFinset]
    exact ⟨hyx, fun hxy => h3 {x, u, y} (is3Clique_triple_iff.mpr ⟨hxu, hxy, huy⟩)⟩
  have hinj : Set.InjOn (fun p : (_ : Fin n) × Fin n => p.2) S := by
    rintro ⟨u, y⟩ hp ⟨u', y'⟩ hp' hyy
    rw [Finset.mem_coe] at hp hp'
    simp only [hSdef, Finset.mem_sigma, Finset.mem_erase, mem_neighborFinset] at hp hp'
    simp only at hyy
    subst hyy
    have huu : u = u' := by
      by_contra hne
      exact h4 x y u u' (Ne.symm hp.2.1) hne hp.1 hp.2.2.symm hp'.1 hp'.2.2.symm
    subst huu
    rfl
  have hsub : G.neighborFinset x ⊆ univ.erase x := by
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rintro rfl
    simp at hu
  have hcard := Finset.card_le_card_of_injOn _ hmem hinj
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin,
    card_neighborFinset_eq_degree] at hcard
  have hScard : #S = ∑ u ∈ G.neighborFinset x, (G.degree u - 1) := by
    rw [hSdef, Finset.card_sigma]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hxu : x ∈ G.neighborFinset u := by
      rw [mem_neighborFinset]
      exact ((mem_neighborFinset _ _ _).mp hu).symm
    rw [Finset.card_erase_of_mem hxu, card_neighborFinset_eq_degree]
  have hpos : ∀ u ∈ G.neighborFinset x, G.degree u - 1 + 1 = G.degree u := by
    intro u hu
    have hxu : x ∈ G.neighborFinset u := by
      rw [mem_neighborFinset]
      exact ((mem_neighborFinset _ _ _).mp hu).symm
    have : 0 < G.degree u := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨x, hxu⟩
    omega
  have hsplit : ∑ u ∈ G.neighborFinset x, G.degree u = #S + G.degree x := by
    calc ∑ u ∈ G.neighborFinset x, G.degree u
        = ∑ u ∈ G.neighborFinset x, ((G.degree u - 1) + 1) :=
          Finset.sum_congr rfl fun u hu => (hpos u hu).symm
      _ = (∑ u ∈ G.neighborFinset x, (G.degree u - 1)) + #(G.neighborFinset x) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = #S + G.degree x := by rw [hScard, card_neighborFinset_eq_degree]
  have hdx : G.degree x ≤ n - 1 := by
    rw [← card_neighborFinset_eq_degree]
    calc #(G.neighborFinset x) ≤ #(univ.erase x : Finset (Fin n)) := Finset.card_le_card hsub
      _ = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  omega

theorem bnd_valid (q : ℕ) :
    SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f (fun n => bnd n q) := by
  intro n
  match n with
  | 0 => exact le_trans (by simpa using SqueezeBench.ExGirthFive.f_le_choose_two 0) (Nat.zero_le _)
  | (k + 1) =>
    refine SqueezeBench.ExGirthFive.f_le_of_forall_cliqueFree_noTwoCommonNeighbours
      (Nat.succ_le_succ (Nat.zero_le k)) fun G _ h3 h4 => ?_
    classical
    simp only [bnd, lo, Nat.add_sub_cancel]
    by_cases hall : ∀ u : Fin (k + 1), G.degree u ≤ q
    · refine le_trans ?_ (le_max_left _ _)
      have h2m : 2 * #G.edgeFinset ≤ (k + 1) * q := by
        rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
        calc ∑ u : Fin (k + 1), G.degree u ≤ ∑ _u : Fin (k + 1), q :=
              Finset.sum_le_sum fun u _ => hall u
          _ = (k + 1) * q := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      set A := (k + 1) * q with hA
      omega
    · refine le_trans ?_ (le_max_right _ _)
      simp only [not_forall, Nat.not_le] at hall
      obtain ⟨v0, hv0⟩ := hall
      obtain ⟨w0, -, hw0⟩ := Finset.exists_min_image (univ : Finset (Fin (k + 1)))
        (fun u => G.degree u) ⟨0, Finset.mem_univ 0⟩
      set D := G.degree w0 with hD
      set L := min (k / (q + 1)) q with hL
      have hnb := nbr_sum_le G h3 h4 v0
      rw [Nat.add_sub_cancel] at hnb
      have hge : G.degree v0 * D ≤ ∑ u ∈ G.neighborFinset v0, G.degree u := by
        calc G.degree v0 * D = ∑ _u ∈ G.neighborFinset v0, D := by
              rw [Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul, mul_comm]
          _ ≤ _ := Finset.sum_le_sum fun u _ => hw0 u (Finset.mem_univ u)
      have hqd : (q + 1) * D ≤ k :=
        le_trans (Nat.mul_le_mul_right D hv0) (le_trans hge hnb)
      have hDle : D ≤ L ∨ L = q := by
        rcases Nat.lt_or_ge q (k / (q + 1)) with h | h
        · right
          rw [hL, min_eq_right (le_of_lt h)]
        · left
          rw [hL, min_eq_left h, Nat.le_div_iff_mul_le (Nat.succ_pos q)]
          calc D * (q + 1) = (q + 1) * D := by ring
            _ ≤ k := hqd
      have hLq : L ≤ q := min_le_right _ _
      have hc2 : (2 * q + 1) * D ≤ D * D + L * (2 * q + 1 - L) := chord2 D L q hLq hDle
      have hQ : 2 * #G.edgeFinset = (∑ u ∈ univ.erase w0, G.degree u) + D := by
        rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, hD]
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ w0)).symm
      have hQ2 : (∑ u : Fin (k + 1), G.degree u ^ 2)
          = (∑ u ∈ univ.erase w0, G.degree u ^ 2) + D * D := by
        rw [hD, ← pow_two]
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ w0)).symm
      have hSS := V001.sum_sq_degree_le G h3 h4
      have hnn : (k + 1) * (k + 1) - (k + 1) = (k + 1) * k := by
        rw [Nat.mul_succ, Nat.add_sub_cancel]
      rw [hnn, hQ2] at hSS
      have hchord : (2 * q + 1) * (∑ u ∈ univ.erase w0, G.degree u)
          ≤ (∑ u ∈ univ.erase w0, G.degree u ^ 2) + k * (q * (q + 1)) := by
        rw [Finset.mul_sum]
        calc ∑ u ∈ univ.erase w0, (2 * q + 1) * G.degree u
            ≤ ∑ u ∈ univ.erase w0, ((G.degree u) ^ 2 + q * (q + 1)) :=
              Finset.sum_le_sum fun u _ => V002.chord _ _
          _ = (∑ u ∈ univ.erase w0, G.degree u ^ 2) + k * (q * (q + 1)) := by
              rw [Finset.sum_add_distrib, Finset.sum_const,
                Finset.card_erase_of_mem (Finset.mem_univ w0), Finset.card_univ,
                Fintype.card_fin, Nat.add_sub_cancel, smul_eq_mul]
      set M := L * (2 * q + 1 - L) with hM
      set Q := ∑ u ∈ univ.erase w0, G.degree u with hQdef
      set Q2 := ∑ u ∈ univ.erase w0, G.degree u ^ 2 with hQ2def
      have key : (2 * q + 1) * (2 * #G.edgeFinset) ≤ M + (k + 1) * k + k * (q * (q + 1)) := by
        calc (2 * q + 1) * (2 * #G.edgeFinset) = (2 * q + 1) * Q + (2 * q + 1) * D := by
              rw [hQ]; ring
          _ ≤ (Q2 + k * (q * (q + 1))) + (D * D + M) := Nat.add_le_add hchord hc2
          _ = (Q2 + D * D) + k * (q * (q + 1)) + M := by ring
          _ ≤ (k + 1) * k + k * (q * (q + 1)) + M := by
              exact Nat.add_le_add_right (Nat.add_le_add_right hSS _) _
          _ = M + (k + 1) * k + k * (q * (q + 1)) := by ring
      refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
      calc #G.edgeFinset * (2 * (2 * q + 1)) = (2 * q + 1) * (2 * #G.edgeFinset) := by ring
        _ ≤ _ := key

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f v := by
  intro n
  simp only [v]
  exact le_min (bnd_valid _ n) (le_min (bnd_valid _ n) (bnd_valid _ n))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExGirthFive.Upper.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V002.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V002.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 18) (by decide)
    (by decide +kernel)

end SqueezeBench.ExGirthFive.Upper.V003
