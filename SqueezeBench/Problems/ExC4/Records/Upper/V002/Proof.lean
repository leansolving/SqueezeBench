import SqueezeBench.Problems.ExC4.Records.Upper.V002.Def
import SqueezeBench.Problems.ExC4.Records.Upper.V001.Proof

/-! Record V002 for ExC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Upper/V002.lean`. -/

namespace SqueezeBench.ExC4.Upper.V002

open Finset SimpleGraph

theorem c2_eq (a : ℕ) : c2 a = a.choose 2 := by
  rw [c2, Nat.choose_two_right]

theorem choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  have h : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
  rw [Nat.choose_one_right] at h
  omega

-- Vandermonde at `2`: `C(m+c,2) = C(m,2) + mc + C(c,2)`.
theorem choose_two_add (m c : ℕ) : (m + c).choose 2 = m.choose 2 + m * c + c.choose 2 := by
  induction c with
  | zero => simp
  | succ c ih =>
      have h : m + (c + 1) = (m + c) + 1 := by ring
      rw [h, choose_two_succ, ih, choose_two_succ]
      ring

-- The tangent line to the convex function `C(·,2)` at `q`; this is all the convexity needed.
theorem tangent (d q : ℕ) : q.choose 2 + q * d ≤ d.choose 2 + q * q := by
  rcases le_total q d with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [choose_two_add]
    have := Nat.zero_le (c.choose 2)
    nlinarith
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [choose_two_add]
    have hc := SqueezeBench.ExC4.Upper.V001.mul_self_eq c
    nlinarith

-- An integral degree sequence with sum `S` on `n` vertices has cherry count at least
-- `n·C(q,2) + q·(S − qn)` with `q = ⌊S/n⌋`; against `Σ C(d,2) ≤ C(n,2)` that is `cherryOk`.
theorem cherryOk_of_free {k : ℕ} (G : SimpleGraph (Fin (k + 1))) [DecidableRel G.Adj]
    (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) :
    cherryOk (k + 1) (2 * #G.edgeFinset) = true := by
  have hdeg : ∑ x : Fin (k + 1), G.degree x = 2 * #G.edgeFinset :=
    G.sum_degrees_eq_twice_card_edges
  obtain ⟨q, hq⟩ : ∃ q, (2 * #G.edgeFinset) / (k + 1) = q := ⟨_, rfl⟩
  have h1 : ∑ x : Fin (k + 1), (q.choose 2 + q * G.degree x)
      ≤ ∑ x : Fin (k + 1), ((G.degree x).choose 2 + q * q) :=
    Finset.sum_le_sum fun x _ => tangent (G.degree x) q
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hdeg] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 := SqueezeBench.ExC4.Upper.V001.sum_choose_degree_le G hG
  rw [cherryOk, decide_eq_true_eq, hq, c2_eq, c2_eq]
  linarith

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record := by
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
      have hu : #G.edgeFinset ≤ SqueezeBench.ExC4.Upper.V001.record (k + 1) :=
        le_trans (SqueezeBench.ExC4.le_f_of_noTwoCommonNeighbours (by simp) hG)
          (SqueezeBench.ExC4.Upper.V001.valid (k + 1))
      rcases Bool.eq_false_or_eq_true
        (cherryOk (k + 1) (2 * SqueezeBench.ExC4.Upper.V001.record (k + 1))) with h | h
      · have hr : record (k + 1) = SqueezeBench.ExC4.Upper.V001.record (k + 1) := by
          simp [record, h]
        omega
      · have hne : #G.edgeFinset ≠ SqueezeBench.ExC4.Upper.V001.record (k + 1) := by
          intro heq
          rw [← heq, cherryOk_of_free G hG] at h
          exact Bool.noConfusion h
        have hr : record (k + 1) = SqueezeBench.ExC4.Upper.V001.record (k + 1) - 1 := by
          simp [record, h]
        omega

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V001.record record := by
  intro n
  simp only [record]
  split <;> omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V001.record record :=
  ⟨15, by decide, by decide +kernel⟩

end SqueezeBench.ExC4.Upper.V002
