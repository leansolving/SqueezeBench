import SqueezeBench.Problems.ExGirthFive.Records.Upper.V001.Def
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V000.Proof

/-! Record V001 for ExGirthFive, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Upper/V001.lean`.

The mathematics is the Moore-type count. In a graph of girth at least `5` two distinct vertices
have at most one common neighbour, and two *adjacent* vertices have none, so the cherries (a
centre with an ordered pair of distinct neighbours) inject into the ordered non-adjacent pairs
while the ordered adjacent pairs fill the rest. Together
`∑ d(w)² = ∑ (d(w)² - d(w)) + ∑ d(w) ≤ n² - n`, and Cauchy-Schwarz turns that into
`(2·#E)² ≤ n·(n² - n)`, i.e. `#E ≤ √(n²(n-1))/2`.
-/

namespace SqueezeBench.ExGirthFive.Upper.V001

open Finset SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

-- A centre together with an ordered pair of distinct neighbours of it.
def cherries : Finset ((_ : Fin n) × (Fin n × Fin n)) :=
  univ.sigma (fun w => (G.neighborFinset w).offDiag)

-- The ordered adjacent pairs.
def arcs : Finset ((_ : Fin n) × Fin n) := univ.sigma (fun w => G.neighborFinset w)

theorem card_cherries :
    (cherries G).card = ∑ w : Fin n, (G.degree w * G.degree w - G.degree w) := by
  simp [cherries, Finset.card_sigma, Finset.offDiag_card]

theorem card_arcs : (arcs G).card = ∑ w : Fin n, G.degree w := by
  simp [arcs, Finset.card_sigma]

-- No triangle: the two ends of a cherry are distinct and non-adjacent.
-- No two common neighbours: the centre is determined by the two ends.
theorem cherries_le (h3 : G.CliqueFree 3)
    (h4 : SqueezeBench.ExGirthFive.NoTwoCommonNeighbours G) :
    (cherries G).card ≤ #{p ∈ (univ : Finset (Fin n)).offDiag | ¬ G.Adj p.1 p.2} := by
  refine Finset.card_le_card_of_injOn (fun s => s.2) ?_ ?_
  · rintro ⟨w, x, y⟩ hs
    simp only [cherries, Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_offDiag, SimpleGraph.mem_neighborFinset] at hs
    obtain ⟨hx, hy, hxy⟩ := hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact ⟨hxy, fun hadj => h3 {w, x, y} (is3Clique_triple_iff.mpr ⟨hx, hy, hadj⟩)⟩
  · rintro ⟨w, x, y⟩ hv ⟨w', x', y'⟩ hw heq
    simp only [cherries, Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_offDiag, SimpleGraph.mem_neighborFinset] at hv hw
    obtain ⟨hvx, hvy, hxy⟩ := hv
    obtain ⟨hwx, hwy, _⟩ := hw
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    by_cases hvw : w = w'
    · subst hvw; rfl
    · exact absurd (h4 x y w w' hxy hvw hvx.symm hvy.symm hwx.symm hwy.symm) not_false

theorem arcs_le : (arcs G).card ≤ #{p ∈ (univ : Finset (Fin n)).offDiag | G.Adj p.1 p.2} := by
  refine Finset.card_le_card_of_injOn (fun s => (s.1, s.2)) ?_ ?_
  · rintro ⟨w, x⟩ hs
    simp only [arcs, Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset] at hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact ⟨hs.ne, hs⟩
  · rintro ⟨w, x⟩ _ ⟨w', y⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

theorem sum_sq_degree_le (h3 : G.CliqueFree 3)
    (h4 : SqueezeBench.ExGirthFive.NoTwoCommonNeighbours G) :
    ∑ w : Fin n, G.degree w ^ 2 ≤ n * n - n := by
  have hsum : (cherries G).card + (arcs G).card ≤ (univ : Finset (Fin n)).offDiag.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n)).offDiag) (p := fun p => G.Adj p.1 p.2)
    have h1 := cherries_le G h3 h4
    have h2 := arcs_le G
    omega
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hsum
  rw [card_cherries, card_arcs] at hsum
  have hd : ∀ w : Fin n, G.degree w ≤ G.degree w * G.degree w := by
    intro w
    rcases Nat.eq_zero_or_pos (G.degree w) with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  have hsq : ∑ w : Fin n, G.degree w ^ 2
      = ∑ w : Fin n, (G.degree w * G.degree w - G.degree w) + ∑ w : Fin n, G.degree w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have := hd w
    rw [sq]
    omega
  omega

-- Cauchy-Schwarz against the degree bound: `(∑ d)² ≤ n · ∑ d²`.
theorem sq_two_mul_card_edgeFinset_le (h3 : G.CliqueFree 3)
    (h4 : SqueezeBench.ExGirthFive.NoTwoCommonNeighbours G) :
    (2 * #G.edgeFinset) ^ 2 ≤ n * (n * n - n) := by
  have hcs : (∑ w : Fin n, G.degree w) ^ 2 ≤ n * ∑ w : Fin n, G.degree w ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n)))
      (f := fun w => G.degree w)
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hcs
  exact hcs.trans (Nat.mul_le_mul_left _ (sum_sq_degree_le G h3 h4))

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f v := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [v] using SqueezeBench.ExGirthFive.f_le_choose_two 0
  · refine SqueezeBench.ExGirthFive.f_le_of_forall_cliqueFree_noTwoCommonNeighbours
      hn fun G _ h3 h4 => ?_
    have h2 : 2 * #G.edgeFinset ≤ Nat.sqrt (n * (n * n - n)) :=
      Nat.le_sqrt'.mpr (sq_two_mul_card_edgeFinset_le G h3 h4)
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExGirthFive.Upper.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V000.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V000.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 10) (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Upper.V001
