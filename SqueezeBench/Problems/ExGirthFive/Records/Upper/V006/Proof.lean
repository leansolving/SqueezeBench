import SqueezeBench.Problems.ExGirthFive.Records.Upper.V006.Def
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V005.Proof

/-! Record V006 for ExGirthFive, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Upper/V006.lean`.

The per-vertex count `∑_{u ~ v} d(u) ≤ N` (`N = n - 1`, V003's `nbr_sum_le`) is weighted
by a function of `d(v)`, as in the dual of the linear program over degree classes. Let `ψ` be
the minimum of finitely many lines with nonnegative slopes (so `ψ` is concave and
nondecreasing). For a vertex `v` of degree `d`, take a line `ℓ = S·x + I` attaining
`ψ(N/d)`: then `∑_{u ~ v} ψ(d(u)) ≤ ∑_{u ~ v} ℓ(d(u)) = S·∑_{u ~ v} d(u) + I·d ≤ S·N + I·d
= d·ψ(N/d)`. If `Λ` satisfies `2·d·ψ(N/d) + Q·d ≤ 2·d·ψ(d) + Λ` for every degree `d ≤ N`
(everything scaled by the common denominator `Q`), summing over `v` and double counting
`∑_v ∑_{u ~ v} ψ(d(u)) = ∑_u d(u)·ψ(d(u))` gives `2Q·m ≤ n·Λ`. The record computes the least
such `Λ` for two explicit families of lines, so no inequality about the lines is needed. -/

namespace SqueezeBench.ExGirthFive.Upper.V006

open Finset SimpleGraph

-- `ψ(N/d)` is attained by one of the five lines, and `ψ ≤` that line everywhere.
theorem psiN_attained (L : Lines) (N d : ℕ) :
    ∃ S I : ℕ, psiN L N d = S * N + I * d ∧ ∀ e, psiD L e ≤ S * e + I := by
  unfold psiN
  rcases min_choice (lineN L.1 N d) (min (lineN L.2.1 N d) (min (lineN L.2.2.1 N d)
      (min (lineN L.2.2.2.1 N d) (lineN L.2.2.2.2 N d)))) with h | h
  · exact ⟨L.1.1, L.1.2, h, fun e => by unfold psiD lineD; omega⟩
  rw [h]
  rcases min_choice (lineN L.2.1 N d) (min (lineN L.2.2.1 N d)
      (min (lineN L.2.2.2.1 N d) (lineN L.2.2.2.2 N d))) with h | h
  · exact ⟨L.2.1.1, L.2.1.2, h, fun e => by unfold psiD lineD; omega⟩
  rw [h]
  rcases min_choice (lineN L.2.2.1 N d) (min (lineN L.2.2.2.1 N d) (lineN L.2.2.2.2 N d))
      with h | h
  · exact ⟨L.2.2.1.1, L.2.2.1.2, h, fun e => by unfold psiD lineD; omega⟩
  rw [h]
  rcases min_choice (lineN L.2.2.2.1 N d) (lineN L.2.2.2.2 N d) with h | h
  · exact ⟨L.2.2.2.1.1, L.2.2.2.1.2, h, fun e => by unfold psiD lineD; omega⟩
  · exact ⟨L.2.2.2.2.1, L.2.2.2.2.2, h, fun e => by unfold psiD lineD; omega⟩

-- The maximum over `0, …, D` dominates every `term` with `d ≤ D`.
theorem term_le_lamAux (L : Lines) (Q N : ℕ) : ∀ D d, d ≤ D → term L Q N d ≤ lamAux L Q N D := by
  intro D
  induction D with
  | zero => intro d hd; rw [Nat.le_zero.mp hd]; exact le_refl _
  | succ D ih =>
    intro d hd
    rcases Nat.lt_or_ge d (D + 1) with h | h
    · exact le_trans (ih d (Nat.lt_succ_iff.mp h)) (le_max_right _ _)
    · rw [Nat.le_antisymm hd h]; exact le_max_left _ _

-- The certificate theorem: `2·Q·m ≤ n·Λ` for any lines `L` and any admissible `Λ`.
theorem cert_main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (h4 : SqueezeBench.ExGirthFive.NoTwoCommonNeighbours G)
    (L : Lines) (Q Λ : ℕ)
    (hΛ : ∀ d, d ≤ n - 1 → 2 * psiN L (n - 1) d + Q * d ≤ 2 * (d * psiD L d) + Λ) :
    2 * Q * #G.edgeFinset ≤ n * Λ := by
  classical
  -- the weighted per-vertex count
  have hv : ∀ v : Fin n, ∑ u ∈ G.neighborFinset v, psiD L (G.degree u)
      ≤ psiN L (n - 1) (G.degree v) := by
    intro v
    obtain ⟨S, I, hEq, hLe⟩ := psiN_attained L (n - 1) (G.degree v)
    rw [hEq]
    calc ∑ u ∈ G.neighborFinset v, psiD L (G.degree u)
        ≤ ∑ u ∈ G.neighborFinset v, (S * G.degree u + I) :=
          Finset.sum_le_sum fun u _ => hLe _
      _ = S * ∑ u ∈ G.neighborFinset v, G.degree u + I * G.degree v := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            card_neighborFinset_eq_degree, smul_eq_mul, mul_comm (G.degree v) I]
      _ ≤ S * (n - 1) + I * G.degree v :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (V003.nbr_sum_le G h3 h4 v)) _
  -- double counting
  have hswap : ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, psiD L (G.degree u)
      = ∑ u : Fin n, G.degree u * psiD L (G.degree u) := by
    rw [V005.sum_nbr_swap G univ (fun u => psiD L (G.degree u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
    congr 1
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    simp [adj_comm]
  have hdeg : ∀ v : Fin n, G.degree v ≤ n - 1 := by
    intro v
    have := G.degree_lt_card_verts v
    rw [Fintype.card_fin] at this
    omega
  have hE : ∑ v : Fin n, G.degree v = 2 * #G.edgeFinset :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h1 : ∑ v : Fin n, (2 * psiN L (n - 1) (G.degree v) + Q * G.degree v)
      ≤ ∑ v : Fin n, (2 * (G.degree v * psiD L (G.degree v)) + Λ) :=
    Finset.sum_le_sum fun v _ => hΛ _ (hdeg v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    hE] at h1
  have h2 : ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, psiD L (G.degree u)
      ≤ ∑ v : Fin n, psiN L (n - 1) (G.degree v) :=
    Finset.sum_le_sum fun v _ => hv v
  rw [hswap] at h2
  set A := ∑ u : Fin n, G.degree u * psiD L (G.degree u)
  set B := ∑ v : Fin n, psiN L (n - 1) (G.degree v)
  set m := #G.edgeFinset
  have h3' : 2 * Q * m = Q * (2 * m) := by ring
  rw [h3']
  omega

theorem certBound_valid (L : Lines) (Q : ℕ) :
    SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f (fun n => certBound L Q n) := by
  intro n
  simp only [certBound]
  split_ifs with hQ
  · have h := SqueezeBench.ExGirthFive.f_le_choose_two n
    rwa [Nat.choose_two_right] at h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact le_trans (by simpa using SqueezeBench.ExGirthFive.f_le_choose_two 0) (Nat.zero_le _)
    refine SqueezeBench.ExGirthFive.f_le_of_forall_cliqueFree_noTwoCommonNeighbours
      hn fun G _ h3 h4 => ?_
    have key := cert_main G h3 h4 L Q (lamAux L Q (n - 1) (n - 1)) fun d hd => by
      have := term_le_lamAux L Q (n - 1) (n - 1) d hd
      unfold term at this
      omega
    have hQpos : 0 < 2 * Q := by omega
    rw [Nat.le_div_iff_mul_le hQpos]
    calc #G.edgeFinset * (2 * Q) = 2 * Q * #G.edgeFinset := by ring
      _ ≤ _ := key

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f v := by
  intro n
  simp only [v, boundA, boundB]
  exact le_min (certBound_valid _ _ n) (certBound_valid _ _ n)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExGirthFive.Upper.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V005.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V005.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 410) (by decide)
    (by decide +kernel)

end SqueezeBench.ExGirthFive.Upper.V006
