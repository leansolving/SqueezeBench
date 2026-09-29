import SqueezeBench.Problems.Ramsey3.Records.Upper.V001.Def
import SqueezeBench.Problems.Ramsey3.Records.Upper.V000.Proof

/-! Record V001 for Ramsey3, upper direction, by baseline claude-opus-5: the three obligations.

The mathematics is the parity refinement of Erdős–Szekeres. Suppose no colouring of `K_N`
with `N = M + N' - 1` vertices has a red `K_{s+1}` or a blue `K_{t+1}`, where `M` forces
`(s, t+1)` and `N'` forces `(s+1, t)`. Then every vertex has red degree `< M` and blue degree
`< N'`, and those two degrees sum to `N - 1 = M + N' - 2`, so the red graph is exactly
`(M-1)`-regular on `M + N' - 1` vertices. If `M` and `N'` are both even that is an odd-regular
graph on an odd number of vertices, which the handshake lemma forbids.

At `s = 2`, `t = k`, the first hypothesis is `M = k + 1` (a red `K_2` or a blue `K_{k+1}`) and
the second is the previous bound on `R(3,k)`. `k + 1` is even exactly when `k` is odd, and the
bound `(k²+3)/2` is then even as well, so the saving lands at every step from an odd `k` to an
even `k + 1`. -/

namespace SqueezeBench.Ramsey3.Upper.V001

open Finset SimpleGraph SqueezeBench SqueezeBench.Ramsey

/-- With no `K_{s+1}` in `G` and no `K_{t+1}` in `Gᶜ`, a vertex cannot have `M` neighbours:
`ForcesOn M s (t+1)` applied inside its neighbourhood would give a clique to extend by it. -/
theorem deg_bound {M s t : ℕ} {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hM : ForcesOn M s (t + 1))
    (hS : ∀ S : Finset V, ¬ G.IsNClique (s + 1) S)
    (hT : ∀ T : Finset V, ¬ Gᶜ.IsNClique (t + 1) T) (v : V) :
    G.degree v < M := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcardA : M ≤ Fintype.card ((G.neighborFinset v : Finset V) : Set V) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    simpa using hcon
  rcases hM (G.induce ((G.neighborFinset v : Finset V) : Set V)) hcardA with ⟨S, hs⟩ | ⟨T, ht⟩
  · rw [isNClique_induce_iff] at hs
    refine hS (insert v (S.map (Function.Embedding.subtype _))) (hs.insert ?_)
    intro b hb
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
    obtain ⟨w, _, rfl⟩ := hb
    simpa using w.2
  · rw [← induce_compl, isNClique_induce_iff] at ht
    exact hT _ ht

/-- The same in the complement. -/
theorem codeg_bound {N s t : ℕ} {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hN : ForcesOn N (s + 1) t)
    (hS : ∀ S : Finset V, ¬ G.IsNClique (s + 1) S)
    (hT : ∀ T : Finset V, ¬ Gᶜ.IsNClique (t + 1) T) (v : V) :
    Gᶜ.degree v < N := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcardB : N ≤ Fintype.card ((Gᶜ.neighborFinset v : Finset V) : Set V) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    simpa using hcon
  rcases hN (G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V)) hcardB with ⟨S, hs⟩ | ⟨T, ht⟩
  · rw [isNClique_induce_iff] at hs
    exact hS _ hs
  · rw [← induce_compl, isNClique_induce_iff] at ht
    refine hT (insert v (T.map (Function.Embedding.subtype _))) (ht.insert ?_)
    intro b hb
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
    obtain ⟨w, _, rfl⟩ := hb
    simpa using w.2

/-- The parity refinement: when `M` and `N` are both even, `M + N - 1` already forces. -/
theorem forcesOn_step_parity {M N s t : ℕ} (h1 : 1 ≤ M) (h2 : 1 ≤ N)
    (hMe : M % 2 = 0) (hNe : N % 2 = 0)
    (hM : ForcesOn M s (t + 1)) (hN : ForcesOn N (s + 1) t) :
    ForcesOn (M + N - 1) (s + 1) (t + 1) := by
  intro V _ _ G hcard
  classical
  haveI : DecidableRel G.Adj := Classical.decRel _
  by_contra hcon
  push_neg at hcon
  obtain ⟨hS, hT⟩ := hcon
  have hreg : ∀ v : V, G.degree v = M - 1 := by
    intro v
    have h3 := deg_bound G hM hS hT v
    have h4 := codeg_bound G hN hS hT v
    have h5 := split_card G v
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h5
    omega
  have hcardV : Fintype.card V = M + N - 1 := by
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have h3 := deg_bound G hM hS hT v
    have h4 := codeg_bound G hN hS hT v
    have h5 := split_card G v
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h5
    omega
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hsum2 : ∑ v : V, G.degree v = Fintype.card V * (M - 1) := by
    rw [Finset.sum_congr rfl (fun v _ => hreg v)]
    simp [Finset.card_univ]
  rw [hsum2, hcardV] at hsum
  -- an odd-regular graph on an odd number of vertices has an odd degree sum
  obtain ⟨m, rfl⟩ : ∃ m, M = 2 * m := ⟨M / 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = 2 * n := ⟨N / 2, by omega⟩
  have hodd : (2 * m + 2 * n - 1) * (2 * m - 1) % 2 = 1 := by
    have e1 : 2 * m + 2 * n - 1 = 2 * (m + n - 1) + 1 := by omega
    have e2 : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [e1, e2]
    have : (2 * (m + n - 1) + 1) * (2 * (m - 1) + 1)
        = 2 * (2 * (m + n - 1) * (m - 1) + (m + n - 1) + (m - 1)) + 1 := by ring
    omega
  omega

/-- A red `K_2` or a blue `K_{k+1}` on `k + 1` vertices: `R(2, k+1) = k + 1`. -/
theorem forcesOn_two {k : ℕ} : ForcesOn (k + 1) 2 (k + 1) := by
  have h : ForcesOn (Nat.choose (1 + k) 1) 2 (k + 1) := Ramsey.forcesOn_choose 1 k
  rwa [Nat.choose_one_right, Nat.add_comm 1 k] at h

/-- The recursion, run from `R(3,2) ≤ 3`. -/
theorem forcesOn_main : ∀ k, 2 ≤ k → ForcesOn ((k * k + 3) / 2) 3 k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact Ramsey.forcesOn_choose 2 1
  | succ k hk ih =>
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨j, hj⟩ := he
        have e1 : k * k = 4 * (j * j) := by subst hj; ring
        have e2 : (k + 1) * (k + 1) = 4 * (j * j) + 4 * j + 1 := by subst hj; ring
        have hEq : ((k + 1) * (k + 1) + 3) / 2 = (k + 1) + (k * k + 3) / 2 := by omega
        rw [hEq]
        show ForcesOn ((k + 1) + (k * k + 3) / 2) (2 + 1) (k + 1)
        exact Ramsey.forcesOn_step (by omega) forcesOn_two ih
      · obtain ⟨j, hj⟩ := ho
        have e1 : k * k = 4 * (j * j) + 4 * j + 1 := by subst hj; ring
        have e2 : (k + 1) * (k + 1) = 4 * (j * j) + 8 * j + 4 := by subst hj; ring
        have hEq : ((k + 1) * (k + 1) + 3) / 2 = (k + 1) + (k * k + 3) / 2 - 1 := by omega
        rw [hEq]
        show ForcesOn ((k + 1) + (k * k + 3) / 2 - 1) (2 + 1) (k + 1)
        exact forcesOn_step_parity (by omega) (by omega) (by omega) (by omega) forcesOn_two ih

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f v := by
  intro k
  rcases Nat.lt_or_ge k SqueezeBench.Ramsey3.nMin with h | h
  · rw [SqueezeBench.Ramsey3.f, if_pos h]
    exact Nat.zero_le _
  · exact SqueezeBench.Ramsey3.f_le_of_forces h
      (Ramsey.forces_of_forcesOn (forcesOn_main k h))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Ramsey3.Upper.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey3.Upper.V000.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Upper.V000.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Ramsey3.Upper.V001
