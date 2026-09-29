import SqueezeBench.Problems.ExGirthFive.Records.Upper.V005.Def
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V004.Proof

/-! Record V005 for ExGirthFive, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Upper/V005.lean`.

V004 applied the per-vertex count `∑_{u ~ x} d(u) ≤ n - 1` at a single vertex of degree
`≥ q + 1`. Here it is summed over the set `H` of *all* such vertices. Write `n - 1 = q² + ρ`,
`T = ∑ (d(u) - q)⁺`, `S = ∑ (q - d(u))⁺`, `h = #H`, so that `2m + S = nq + T` and `h ≤ T`.
Double counting the summed constraint by the number `a(u)` of neighbours of `u` inside `H`
gives `q(hq + T) ≤ ∑ d(u)·a(u) + ∑ (q - d(u))⁺·a(u) ≤ h(n - 1) + (q - 1)·S`, because a vertex
with `d(u) < q` has `a(u) ≤ d(u) ≤ q - 1`. Combined with the chord sum with its slack,
`(2q+1)·2m + 2S ≤ n(n-1) + nq(q+1)` (V004's `chordDef`), this eliminates `S`, `T`, `h` and
leaves `(ρ(2q-1) - 1)·2m ≤ (ρ(2q-1) - 1)·nq + nρ(ρ-1)`. -/

namespace SqueezeBench.ExGirthFive.Upper.V005

open Finset SimpleGraph

-- The chord of `x ↦ x²` at `q` with slack `2(q - d)⁺`: V004's `chordDef` below `q`, V002's
-- `chord` above it.
theorem chord_slack (d q : ℕ) : (2 * q + 1) * d + 2 * (q - d) ≤ d * d + q * (q + 1) := by
  rcases Nat.le_total d q with h | h
  · have h1 := V004.chordDef d q
    have h2 : 2 * (q - d) + 2 * d = 2 * q := by omega
    set A := (2 * q + 1) * d
    set B := d * d + q * (q + 1)
    omega
  · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero]
    have := V002.chord d q
    rwa [pow_two] at this

-- Summing a function over the neighbourhoods of the vertices of `H` counts each vertex `u`
-- once per neighbour it has inside `H`.
theorem sum_nbr_swap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Fin n)) (g : Fin n → ℕ) :
    ∑ x ∈ H, ∑ u ∈ G.neighborFinset x, g u
      = ∑ u : Fin n, g u * #(H.filter fun x => G.Adj x u) := by
  classical
  have h1 : ∀ x, ∑ u ∈ G.neighborFinset x, g u = ∑ u : Fin n, if G.Adj x u then g u else 0 := by
    intro x
    rw [neighborFinset_eq_filter, Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

-- The number of neighbours of `u` inside `H` is at most its degree.
theorem card_filter_adj_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Fin n)) (u : Fin n) :
    #(H.filter fun x => G.Adj x u) ≤ G.degree u := by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_le_card fun x hx => ?_
  rw [Finset.mem_filter] at hx
  rw [mem_neighborFinset]
  exact hx.2.symm

-- The final arithmetic: eliminate `S`, `T` and `h` from the four inequalities.
theorem arith (E S T h n q ρ : ℕ) (hq : 1 ≤ q) (hρ : 1 ≤ ρ) (hn : n - 1 = q * q + ρ)
    (hI : E + S = n * q + T)
    (hA : (2 * q + 1) * E + 2 * S ≤ n * (n - 1) + n * (q * (q + 1)))
    (hB : q * q * h + q * T ≤ h * (n - 1) + (q - 1) * S)
    (hH : h ≤ T) :
    (ρ * (2 * q - 1) - 1) * E ≤ (ρ * (2 * q - 1) - 1) * (n * q) + n * ρ * (ρ - 1) := by
  rw [hn] at hA hB
  have h2q : 1 ≤ 2 * q - 1 := by omega
  have hD : 1 ≤ ρ * (2 * q - 1) := by
    calc 1 = 1 * 1 := rfl
      _ ≤ ρ * (2 * q - 1) := Nat.mul_le_mul hρ h2q
  have h2q' : 1 ≤ 2 * q := by omega
  zify [hq, hρ, h2q', hD] at hA hB hH hI ⊢
  have hρ0 : (0 : ℤ) ≤ (ρ : ℤ) - 1 := by linarith
  have hA2 := mul_le_mul_of_nonneg_left hA hρ0
  have hH2 := mul_le_mul_of_nonneg_right hH (by positivity : (0 : ℤ) ≤ ρ)
  nlinarith [hA2, hB, hH2, hI]

-- The main inequality: `(ρ(2q-1) - 1)·2m ≤ (ρ(2q-1) - 1)·nq + nρ(ρ-1)` when `n - 1 = q² + ρ`.
theorem main_ineq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (h4 : SqueezeBench.ExGirthFive.NoTwoCommonNeighbours G)
    (q ρ : ℕ) (hq : 1 ≤ q) (hρ : 1 ≤ ρ) (hn : n - 1 = q * q + ρ) :
    (ρ * (2 * q - 1) - 1) * (2 * #G.edgeFinset)
      ≤ (ρ * (2 * q - 1) - 1) * (n * q) + n * ρ * (ρ - 1) := by
  classical
  set H : Finset (Fin n) := univ.filter fun x => q < G.degree x with hHdef
  set S : ℕ := ∑ u : Fin n, (q - G.degree u) with hSdef
  set T : ℕ := ∑ u : Fin n, (G.degree u - q) with hTdef
  have hE : 2 * #G.edgeFinset = ∑ u : Fin n, G.degree u :=
    (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
  have hnq : n * q = ∑ _u : Fin n, q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- the degree identity `2m + S = nq + T`
  have hI : 2 * #G.edgeFinset + S = n * q + T := by
    rw [hE, hnq, hSdef, hTdef, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by omega
  -- the chord sum with its slack
  have hA : (2 * q + 1) * (2 * #G.edgeFinset) + 2 * S
      ≤ n * (n - 1) + n * (q * (q + 1)) := by
    have hsq := V001.sum_sq_degree_le G h3 h4
    have hnn : n * n - n = n * (n - 1) := by rw [Nat.mul_sub_one]
    rw [hnn] at hsq
    have hpt := Finset.sum_le_sum (s := (univ : Finset (Fin n)))
      (f := fun u => (2 * q + 1) * G.degree u + 2 * (q - G.degree u))
      (g := fun u => G.degree u * G.degree u + q * (q + 1))
      fun u _ => chord_slack (G.degree u) q
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hpt
    rw [hE, hSdef]
    calc (2 * q + 1) * ∑ u : Fin n, G.degree u + 2 * ∑ u : Fin n, (q - G.degree u)
        ≤ ∑ u : Fin n, G.degree u * G.degree u + n * (q * (q + 1)) := hpt
      _ ≤ n * (n - 1) + n * (q * (q + 1)) := by
          refine Nat.add_le_add_right ?_ _
          calc ∑ u : Fin n, G.degree u * G.degree u = ∑ u : Fin n, G.degree u ^ 2 := by
                simp [pow_two]
            _ ≤ n * (n - 1) := hsq
  -- each vertex of `H` contributes at least one to `T`
  have hH : #H ≤ T := by
    rw [Finset.card_eq_sum_ones, hTdef, hHdef, Finset.sum_filter]
    exact Finset.sum_le_sum fun u _ => by split_ifs <;> omega
  -- the summed per-vertex count, double counted
  have hB : q * q * #H + q * T ≤ #H * (n - 1) + (q - 1) * S := by
    -- `a u` is the number of neighbours of `u` inside `H`
    set a : Fin n → ℕ := fun u => #(H.filter fun x => G.Adj x u) with hadef
    have hsum : ∑ x ∈ H, ∑ u ∈ G.neighborFinset x, G.degree u ≤ #H * (n - 1) := by
      calc ∑ x ∈ H, ∑ u ∈ G.neighborFinset x, G.degree u ≤ ∑ _x ∈ H, (n - 1) :=
            Finset.sum_le_sum fun x _ => V003.nbr_sum_le G h3 h4 x
        _ = #H * (n - 1) := by rw [Finset.sum_const, smul_eq_mul]
    rw [sum_nbr_swap] at hsum
    -- `∑ a u = ∑_{x ∈ H} d x = q·h + T`
    have hcount : ∑ u : Fin n, a u = q * #H + T := by
      have h1 : ∑ u : Fin n, a u = ∑ x ∈ H, ∑ u ∈ G.neighborFinset x, (1 : ℕ) := by
        rw [sum_nbr_swap]
        simp [hadef]
      rw [h1]
      have h2 : ∀ x, ∑ u ∈ G.neighborFinset x, (1 : ℕ) = G.degree x := by
        intro x
        rw [Finset.sum_const, smul_eq_mul, mul_one, card_neighborFinset_eq_degree]
      simp_rw [h2]
      have h3' : ∀ x ∈ H, G.degree x = q + (G.degree x - q) := by
        intro x hx
        rw [hHdef, Finset.mem_filter] at hx
        omega
      rw [Finset.sum_congr rfl h3', Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        hTdef, hHdef, Finset.sum_filter]
      congr 1
      · exact mul_comm _ _
      · exact Finset.sum_congr rfl fun u _ => by split_ifs <;> omega
    have hpt : ∀ u : Fin n, q * a u ≤ G.degree u * a u + (q - G.degree u) * (q - 1) := by
      intro u
      have hau : a u ≤ G.degree u := card_filter_adj_le G H u
      rcases Nat.lt_or_ge (G.degree u) q with h | h
      · have h1 : q * a u = G.degree u * a u + (q - G.degree u) * a u := by
          rw [← Nat.add_mul, Nat.add_sub_cancel' h.le]
        rw [h1]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      · rw [Nat.sub_eq_zero_of_le h, Nat.zero_mul, Nat.add_zero]
        exact Nat.mul_le_mul_right _ h
    calc q * q * #H + q * T = q * (q * #H + T) := by ring
      _ = q * ∑ u : Fin n, a u := by rw [hcount]
      _ = ∑ u : Fin n, q * a u := by rw [Finset.mul_sum]
      _ ≤ ∑ u : Fin n, (G.degree u * a u + (q - G.degree u) * (q - 1)) :=
          Finset.sum_le_sum fun u _ => hpt u
      _ = ∑ u : Fin n, G.degree u * a u + (∑ u : Fin n, (q - G.degree u)) * (q - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ #H * (n - 1) + (q - 1) * S := by
          rw [hSdef, mul_comm _ (q - 1)]
          exact Nat.add_le_add_right hsum _
  exact arith _ _ _ _ _ _ _ hq hρ hn hI hA hB hH

theorem bnd_valid (q : ℕ) :
    SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f (fun n => bnd n q) := by
  intro n
  simp only [bnd]
  split_ifs with hD
  · have h := SqueezeBench.ExGirthFive.f_le_choose_two n
    rwa [Nat.choose_two_right] at h
  · have hn : 1 ≤ n := by
      rcases n with _ | n
      · simp [den, rho] at hD
      · omega
    refine SqueezeBench.ExGirthFive.f_le_of_forall_cliqueFree_noTwoCommonNeighbours
      hn fun G _ h3 h4 => ?_
    have hρ : 1 ≤ rho n q := by
      by_contra h
      have h0 : rho n q = 0 := by omega
      simp [den, h0] at hD
    have hq : 1 ≤ q := by
      by_contra h
      have h0 : q = 0 := by omega
      simp [den, h0] at hD
    have hn' : n - 1 = q * q + rho n q := by
      unfold rho at hρ ⊢
      set Q := q * q
      omega
    have key := main_ineq G h3 h4 q (rho n q) hq hρ hn'
    have hDpos : 0 < 2 * den n q := by omega
    rw [Nat.le_div_iff_mul_le hDpos]
    calc #G.edgeFinset * (2 * den n q) = den n q * (2 * #G.edgeFinset) := by ring
      _ ≤ den n q * (n * q) + n * rho n q * (rho n q - 1) := by
          unfold den
          exact key

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f v := by
  intro n
  exact bnd_valid _ n

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExGirthFive.Upper.V004.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V004.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V004.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 11) (by decide)
    (by decide +kernel)

end SqueezeBench.ExGirthFive.Upper.V005
