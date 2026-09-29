import SqueezeBench.Problems.HypercubeC4.Records.Upper.V002.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V001.Proof

/-! Record V002 for HypercubeC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V002.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V002

open Finset SimpleGraph

-- The corner of the square at `x` opposite to `x`, in directions `i` and `j`.
def opp {n : ℕ} (x : Fin n → Bool) (i j : Fin n) : Fin n → Bool := flip (flip x i) j

theorem opp_flip_left {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    flip (opp x i j) i = flip x j := by
  funext k
  by_cases h1 : k = i <;> by_cases h2 : k = j <;>
    simp_all [opp, flip_apply, hij, Ne.symm hij]

theorem opp_flip_right {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    flip (opp x i j) j = flip x i := by
  funext k
  by_cases h1 : k = i <;> by_cases h2 : k = j <;>
    simp_all [opp, flip_apply, hij, Ne.symm hij]

theorem opp_opp {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    opp (opp x i j) i j = x := by
  funext k
  by_cases h1 : k = i <;> by_cases h2 : k = j <;>
    simp_all [opp, flip_apply, hij, Ne.symm hij]

-- The words whose edge in direction `i` is present in `G`; each edge is counted at both ends.
def A {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i : Fin n) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => G.Adj x (flip x i))

def cnt {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i : Fin n) : ℕ :=
  #(A G i)

-- A word whose edges in both directions `i` and `j` are present cannot have its opposite
-- corner in the same position: that would close the square.
theorem card_inter_le {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) :
    2 * #(A G i ∩ A G j) ≤ 2 ^ n := by
  have hnot : ∀ x ∈ A G i ∩ A G j, opp x i j ∉ A G i ∩ A G j := by
    intro x hx hox
    simp only [A, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx hox
    refine hG ⟨x, i, j, hij, hx.1, hx.2, ?_, ?_⟩
    · have h := hox.2
      rw [opp_flip_right x hij] at h
      exact h.symm
    · have h := hox.1
      rw [opp_flip_left x hij] at h
      exact h.symm
  have hinj : Set.InjOn (fun x => opp x i j) ↑(A G i ∩ A G j) := by
    intro a _ b _ hab
    have h := congrArg (fun y => opp y i j) hab
    simpa [opp_opp _ hij] using h
  have hdisj : Disjoint (A G i ∩ A G j) ((A G i ∩ A G j).image (fun x => opp x i j)) := by
    rw [Finset.disjoint_right]
    intro y hy hyT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hnot x hx hyT
  have hcard : #(A G i ∩ A G j) + #((A G i ∩ A G j).image (fun x => opp x i j))
      ≤ Fintype.card (Fin n → Bool) := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  rw [Finset.card_image_of_injOn hinj] at hcard
  have h2 : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  omega

-- Two directions carry at most three quarters of their `2ⁿ⁺¹` directed edges.
theorem cnt_add_le {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) :
    2 * (cnt G i + cnt G j) ≤ 3 * 2 ^ n := by
  have hu : #(A G i ∪ A G j) + #(A G i ∩ A G j) = #(A G i) + #(A G j) :=
    Finset.card_union_add_card_inter _ _
  have hle : #(A G i ∪ A G j) ≤ 2 ^ n := by
    have h := Finset.card_le_univ (A G i ∪ A G j)
    have h2 : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
    exact h2 ▸ h
  have hi := card_inter_le G hG hij
  simp only [cnt]
  omega

theorem degree_eq' {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (x : Fin n → Bool) :
    G.degree x = #(Finset.univ.filter (fun i : Fin n => G.Adj x (flip x i))) := by
  rw [SimpleGraph.degree]
  refine (Finset.card_bij (fun i _ => flip x i) ?_ ?_ ?_).symm
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ha
  · intro a _ b _ hab
    exact V001.flip_injective x hab
  · intro y hy
    have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    obtain ⟨i, rfl⟩ := hypercube_adj_iff.mp (hle hadj)
    exact ⟨i, by simp [Finset.mem_filter, hadj], rfl⟩

-- Handshake, split by direction.
theorem two_mul_edges {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) :
    2 * #G.edgeFinset = ∑ i : Fin n, cnt G i := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [Finset.sum_congr rfl (fun x _ => degree_eq' G hle x)]
  simp only [cnt, A, Finset.card_filter]
  exact Finset.sum_comm

-- The double count over ordered pairs of distinct directions.
theorem main {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) :
    #G.edgeFinset ≤ 3 * n * 2 ^ (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hrow : ∀ i : Fin (m + 3),
      ∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j) ≤ (m + 2) * (3 * 2 ^ (m + 3)) := by
    intro i
    calc ∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j)
        ≤ ∑ _j ∈ Finset.univ.erase i, 3 * 2 ^ (m + 3) :=
          Finset.sum_le_sum fun j hj => cnt_add_le G hG (Ne.symm (Finset.ne_of_mem_erase hj))
      _ = (m + 2) * (3 * 2 ^ (m + 3)) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
          congr 1
  have hfull : ∀ i : Fin (m + 3), ∑ j : Fin (m + 3), 2 * (cnt G i + cnt G j)
      = 2 * (m + 3) * cnt G i + 2 * ∑ j : Fin (m + 3), cnt G j := by
    intro i
    have h1 : ∀ j : Fin (m + 3), 2 * (cnt G i + cnt G j) = 2 * cnt G i + 2 * cnt G j :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
    ring
  have herase : ∀ i : Fin (m + 3),
      (∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j)) + 2 * (cnt G i + cnt G i)
        = ∑ j : Fin (m + 3), 2 * (cnt G i + cnt G j) :=
    fun i => Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have h2 : ∀ i : Fin (m + 3),
      (∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j)) + 4 * cnt G i
        = 2 * (m + 3) * cnt G i + 2 * ∑ j : Fin (m + 3), cnt G j := by
    intro i
    rw [← hfull i, ← herase i]; ring
  have htot : (∑ i : Fin (m + 3), ∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j))
      + 4 * ∑ i : Fin (m + 3), cnt G i = 4 * (m + 3) * ∑ i : Fin (m + 3), cnt G i := by
    calc (∑ i : Fin (m + 3), ∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j))
          + 4 * ∑ i : Fin (m + 3), cnt G i
        = ∑ i : Fin (m + 3),
            ((∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j)) + 4 * cnt G i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ _i : Fin (m + 3),
            (2 * (m + 3) * cnt G _i + 2 * ∑ j : Fin (m + 3), cnt G j) :=
          Finset.sum_congr rfl fun i _ => h2 i
      _ = 4 * (m + 3) * ∑ i : Fin (m + 3), cnt G i := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
          ring
  have hbound : (∑ i : Fin (m + 3), ∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j))
      ≤ (m + 3) * ((m + 2) * (3 * 2 ^ (m + 3))) := by
    calc (∑ i : Fin (m + 3), ∑ j ∈ Finset.univ.erase i, 2 * (cnt G i + cnt G j))
        ≤ ∑ _i : Fin (m + 3), (m + 2) * (3 * 2 ^ (m + 3)) := Finset.sum_le_sum fun i _ => hrow i
      _ = (m + 3) * ((m + 2) * (3 * 2 ^ (m + 3))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hE := two_mul_edges G hle
  have hpow : (2 : ℕ) ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; ring
  -- `4 · n · Σ cnt ≤ n(n−1) · 3 · 2ⁿ + 4 · Σ cnt`, with `Σ cnt = 2 · #edges`
  have hstep : 8 * ((m + 2) * #G.edgeFinset) + 8 * #G.edgeFinset
      ≤ (m + 2) * (24 * ((m + 3) * 2 ^ m)) + 8 * #G.edgeFinset := by
    have hle2 : 4 * (m + 3) * ∑ i : Fin (m + 3), cnt G i
        ≤ (m + 3) * ((m + 2) * (3 * 2 ^ (m + 3))) + 4 * ∑ i : Fin (m + 3), cnt G i :=
      htot ▸ Nat.add_le_add_right hbound _
    rw [← hE] at hle2
    rw [hpow] at hle2
    calc 8 * ((m + 2) * #G.edgeFinset) + 8 * #G.edgeFinset
        = 4 * (m + 3) * (2 * #G.edgeFinset) := by ring
      _ ≤ (m + 3) * ((m + 2) * (3 * (8 * 2 ^ m))) + 4 * (2 * #G.edgeFinset) := hle2
      _ = (m + 2) * (24 * ((m + 3) * 2 ^ m)) + 8 * #G.edgeFinset := by ring
  have hcancel : (m + 2) * (8 * #G.edgeFinset) ≤ (m + 2) * (24 * ((m + 3) * 2 ^ m)) := by
    have h := Nat.le_of_add_le_add_right hstep
    calc (m + 2) * (8 * #G.edgeFinset) = 8 * ((m + 2) * #G.edgeFinset) := by ring
      _ ≤ (m + 2) * (24 * ((m + 3) * 2 ^ m)) := h
  have h8 : 8 * #G.edgeFinset ≤ 8 * (3 * ((m + 3) * 2 ^ m)) := by
    have h := Nat.le_of_mul_le_mul_left hcancel (by omega : 0 < m + 2)
    calc 8 * #G.edgeFinset ≤ 24 * ((m + 3) * 2 ^ m) := h
      _ = 8 * (3 * ((m + 3) * 2 ^ m)) := by ring
  have hfin := Nat.le_of_mul_le_mul_left h8 (by norm_num : 0 < 8)
  calc #G.edgeFinset ≤ 3 * ((m + 3) * 2 ^ m) := hfin
    _ = 3 * (m + 3) * 2 ^ (m + 3 - 3) := by rw [Nat.add_sub_cancel]; ring

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f v := by
  intro n
  by_cases hn : 3 ≤ n
  · show SqueezeBench.HypercubeC4.f n ≤ 3 * n * 2 ^ (n - 3)
    exact f_le_of_forall_not_hasSquare (by rw [nMin_eq]; omega) fun G _ hle hG => main hn G hle hG
  · refine (V001.valid n).trans ?_
    show n * 2 ^ (n - 1) ≤ 3 * n * 2 ^ (n - 3)
    interval_cases n <;> norm_num

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.minWith_valid V001.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V001.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V001.record record :=
  SqueezeBench.minWith_strict (n₀ := 5) (by decide) (by decide)

end SqueezeBench.HypercubeC4.Upper.V002
