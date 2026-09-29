import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V001.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V000.Proof

/-! Record V001 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V001.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V001

open Finset SimpleGraph

-- Every edge of a locally linear graph lies in exactly one triangle, so the triangles are
-- edge-disjoint and together use `3 * T` distinct edges out of the `C(n, 2)` there are.
theorem three_mul_le_choose_two (n : ℕ) : 3 * ruzsaSzemerediNumberNat n ≤ n.choose 2 := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  have h1 : 3 * #(G.cliqueFinset 3) ≤ #G.edgeFinset :=
    hLL.edgeDisjointTriangles.card_edgeFinset_le
  have h2 : #G.edgeFinset ≤ (Fintype.card (Fin n)).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  rw [Fintype.card_fin] at h2
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  exact le_trans h1 h2

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · rw [SqueezeBench.RuzsaSzemeredi.f_of_le h]
    rw [show record n = n.choose 2 / 3 from rfl]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := three_mul_le_choose_two n
    omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V000.record record := by
  intro n
  show n.choose 2 / 3 ≤ n.choose 3
  rcases lt_or_ge n 3 with h | h
  · interval_cases n <;> simp
  · have key : n.choose 3 * 3 = n.choose 2 * (n - 2) := Nat.choose_succ_right_eq n 2
    have h1 : 1 ≤ n - 2 := by omega
    have : n.choose 2 ≤ n.choose 3 * 3 := by
      rw [key]
      exact Nat.le_mul_of_pos_right _ h1
    omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V000.record record :=
  ⟨6, by decide, by decide⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V001
