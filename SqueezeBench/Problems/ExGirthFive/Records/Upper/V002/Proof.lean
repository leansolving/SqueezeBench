import SqueezeBench.Problems.ExGirthFive.Records.Upper.V002.Def
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V001.Proof

/-! Record V002 for ExGirthFive, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Upper/V002.lean`.

V001 fed `∑ d(w)² ≤ n² - n` to Cauchy-Schwarz. Here the same inequality is read off against the
chord of `x ↦ x²` through `(q, q²)` and `(q+1, (q+1)²)`, which lies below the parabola at every
*natural* `x`: `(2q+1)·d ≤ d² + q(q+1)`. Summing over the vertices,
`(2q+1)·2m ≤ ∑ d(w)² + n·q(q+1) ≤ n·(n-1+q²+q)` for every `q`, so
`m ≤ ⌊n(n-1+q²+q) / (2(2q+1))⌋`. The best real `q` reproduces Cauchy-Schwarz; the integrality of
`q` and the floor gain a unit whenever the optimal average degree is far from an integer.
-/

namespace SqueezeBench.ExGirthFive.Upper.V002

open Finset SimpleGraph

-- The chord of `x ↦ x²` at `q` lies below the parabola at every natural number.
theorem chord (d q : ℕ) : (2 * q + 1) * d ≤ d ^ 2 + q * (q + 1) := by
  rcases Nat.lt_or_ge q d with h | h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt h
    nlinarith [Nat.zero_le (t * t)]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith [Nat.zero_le (t * t)]

theorem bnd_valid (q : ℕ) :
    SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f (fun n => bnd n q) := by
  intro n
  match n with
  | 0 => simpa [bnd] using SqueezeBench.ExGirthFive.f_le_choose_two 0
  | (k + 1) =>
    refine SqueezeBench.ExGirthFive.f_le_of_forall_cliqueFree_noTwoCommonNeighbours
      (Nat.succ_le_succ (Nat.zero_le k)) fun G _ h3 h4 => ?_
    have hdeg := V001.sum_sq_degree_le G h3 h4
    have hnn : (k + 1) * (k + 1) - (k + 1) = (k + 1) * k := by
      rw [Nat.mul_succ, Nat.add_sub_cancel]
    rw [hnn] at hdeg
    have hch : (2 * q + 1) * (∑ w : Fin (k + 1), G.degree w)
        ≤ (∑ w : Fin (k + 1), G.degree w ^ 2) + (k + 1) * (q * (q + 1)) := by
      rw [Finset.mul_sum]
      calc ∑ w : Fin (k + 1), (2 * q + 1) * G.degree w
          ≤ ∑ _w : Fin (k + 1), ((G.degree _w) ^ 2 + q * (q + 1)) :=
            Finset.sum_le_sum (fun w _ => chord _ _)
        _ = (∑ w : Fin (k + 1), G.degree w ^ 2) + (k + 1) * (q * (q + 1)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul]
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hch
    have key : (2 * q + 1) * (2 * #G.edgeFinset) ≤ (k + 1) * (k + q * q + q) := by
      have hexp : (k + 1) * (k + q * q + q) = (k + 1) * k + (k + 1) * (q * (q + 1)) := by ring
      omega
    refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
    have hcomm : #G.edgeFinset * (2 * (2 * q + 1)) = (2 * q + 1) * (2 * #G.edgeFinset) := by ring
    rw [hcomm]
    simpa using key

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f v := by
  intro n
  simp only [v]
  exact le_min (bnd_valid _ n) (le_min (bnd_valid _ n) (bnd_valid _ n))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExGirthFive.Upper.V001.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V001.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V001.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 15) (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Upper.V002
