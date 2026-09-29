import SqueezeBench.Problems.HypercubeC4.Records.Upper.V005.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V004.Proof

/-! Record V005 for HypercubeC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V005.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V005

open Finset SimpleGraph

/-! ## Flips -/

theorem flip_comm {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    flip (flip x i) j = flip (flip x j) i := by
  funext k
  by_cases h1 : k = i <;> by_cases h2 : k = j <;> simp_all [flip_apply]

theorem flip_inj {n : ℕ} {x y : Fin n → Bool} {i : Fin n} (h : flip x i = flip y i) : x = y := by
  have := congrArg (fun z => flip z i) h
  simpa using this

theorem opp_flip {n : ℕ} (y : Fin n → Bool) (i j : Fin n) :
    V002.opp (flip y i) i j = flip y j := by
  show flip (flip (flip y i) i) j = flip y j
  rw [flip_flip]

/-! ## Membership in the direction sets -/

theorem mem_A {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i : Fin n)
    (x : Fin n → Bool) : x ∈ V002.A G i ↔ G.Adj x (flip x i) := by
  simp [V002.A]

theorem flip_mem_A {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] {i : Fin n}
    {x : Fin n → Bool} (hx : x ∈ V002.A G i) : flip x i ∈ V002.A G i := by
  rw [mem_A] at hx ⊢
  rw [flip_flip]
  exact hx.symm

-- The `j`-edge at `flip x i` is the `j`-edge at the opposite corner.
theorem opp_mem_A_right {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    {i j : Fin n} (hij : i ≠ j) (x : Fin n → Bool) :
    flip x i ∈ V002.A G j → V002.opp x i j ∈ V002.A G j := by
  rw [mem_A, mem_A, V002.opp_flip_right x hij]
  exact fun h => h.symm

-- The `i`-edge at `flip x j` is the `i`-edge at the opposite corner.
theorem opp_mem_A_left {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    {i j : Fin n} (hij : i ≠ j) (x : Fin n → Bool) :
    flip x j ∈ V002.A G i → V002.opp x i j ∈ V002.A G i := by
  intro h
  rw [mem_A] at h ⊢
  rw [V002.opp_flip_left x hij]
  have : flip (flip x j) i = V002.opp x i j := (flip_comm x i j).symm
  rw [this] at h
  exact h.symm

-- V002's involution: a corner with both edges forbids the opposite corner from having both.
theorem opp_not_mem {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) {x : Fin n → Bool}
    (hx : x ∈ V002.A G i ∩ V002.A G j) : V002.opp x i j ∉ V002.A G i ∩ V002.A G j := by
  intro hox
  simp only [Finset.mem_inter, mem_A] at hx hox
  refine hG ⟨x, i, j, hij, hx.1, hx.2, ?_, ?_⟩
  · have h := hox.2
    rw [V002.opp_flip_right x hij] at h
    exact h.symm
  · have h := hox.1
    rw [V002.opp_flip_left x hij] at h
    exact h.symm

/-! ## The local inequality `3·#(A i ∩ A j) ≤ cnt i + cnt j` -/

theorem three_mul_card_inter_le {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) :
    3 * #(V002.A G i ∩ V002.A G j) ≤ V002.cnt G i + V002.cnt G j := by
  have hsub : V002.A G i ∩ V002.A G j ⊆ V002.A G i ∪ V002.A G j :=
    Finset.inter_subset_left.trans Finset.subset_union_left
  -- `ψ` sends a corner with both edges to a corner of the same square with exactly one.
  set ψ : (Fin n → Bool) → (Fin n → Bool) := fun x =>
    if V002.opp x i j ∈ V002.A G i ∪ V002.A G j then V002.opp x i j else flip x i with hψ
  have hmaps : ∀ x ∈ V002.A G i ∩ V002.A G j,
      ψ x ∈ (V002.A G i ∪ V002.A G j) \ (V002.A G i ∩ V002.A G j) := by
    intro x hx
    by_cases hc : V002.opp x i j ∈ V002.A G i ∪ V002.A G j
    · simp only [hψ, if_pos hc]
      exact Finset.mem_sdiff.mpr ⟨hc, opp_not_mem G hG hij hx⟩
    · simp only [hψ, if_neg hc]
      have hxi : x ∈ V002.A G i := (Finset.mem_inter.mp hx).1
      have h1 : flip x i ∈ V002.A G i := flip_mem_A G hxi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ h1, ?_⟩
      intro hmem
      exact hc (Finset.mem_union_right _
        (opp_mem_A_right G hij x (Finset.mem_inter.mp hmem).2))
  have hinj : Set.InjOn ψ ↑(V002.A G i ∩ V002.A G j) := by
    intro a ha b hb hab
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at ha hb
    by_cases hca : V002.opp a i j ∈ V002.A G i ∪ V002.A G j <;>
      by_cases hcb : V002.opp b i j ∈ V002.A G i ∪ V002.A G j
    · simp only [hψ, if_pos hca, if_pos hcb] at hab
      have := congrArg (fun z => V002.opp z i j) hab
      simpa [V002.opp_opp _ hij] using this
    · -- `a` uses the opposite corner, `b` uses `flip b i`
      exfalso
      simp only [hψ, if_pos hca, if_neg hcb] at hab
      have ha2 : a = flip b j := by
        have := congrArg (fun z => V002.opp z i j) hab
        simp only [V002.opp_opp _ hij] at this
        rw [this, opp_flip]
      apply hcb
      refine Finset.mem_union_left _ (opp_mem_A_left G hij b ?_)
      rw [← ha2]
      exact ha.1
    · exfalso
      simp only [hψ, if_neg hca, if_pos hcb] at hab
      have hb2 : b = flip a j := by
        have := congrArg (fun z => V002.opp z i j) hab.symm
        simp only [V002.opp_opp _ hij] at this
        rw [this, opp_flip]
      apply hca
      refine Finset.mem_union_left _ (opp_mem_A_left G hij a ?_)
      rw [← hb2]
      exact hb.1
    · simp only [hψ, if_neg hca, if_neg hcb] at hab
      exact flip_inj hab
  have hcard : #(V002.A G i ∩ V002.A G j)
      ≤ #((V002.A G i ∪ V002.A G j) \ (V002.A G i ∩ V002.A G j)) :=
    Finset.card_le_card_of_injOn ψ hmaps hinj
  have hsplit : #((V002.A G i ∪ V002.A G j) \ (V002.A G i ∩ V002.A G j))
      + #(V002.A G i ∩ V002.A G j) = #(V002.A G i ∪ V002.A G j) :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hu : #(V002.A G i ∪ V002.A G j) + #(V002.A G i ∩ V002.A G j)
      = #(V002.A G i) + #(V002.A G j) := Finset.card_union_add_card_inter _ _
  simp only [V002.cnt]
  omega

/-! ## The bound -/

theorem main {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) :
    3 * #G.edgeFinset ≤ (2 * n + 1) * 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hE := V002.two_mul_edges G hle
  have hrow : ∀ i : Fin (k + 2), 3 * ∑ j : Fin (k + 2), #(V002.A G i ∩ V002.A G j)
      ≤ 2 * V002.cnt G i + ((k + 1) * V002.cnt G i + ∑ j : Fin (k + 2), V002.cnt G j) := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Nat.mul_add]
    have h1 : #(V002.A G i ∩ V002.A G i) = V002.cnt G i := by rw [Finset.inter_self]; rfl
    have h2 : 3 * ∑ j ∈ Finset.univ.erase i, #(V002.A G i ∩ V002.A G j)
        ≤ ∑ j ∈ Finset.univ.erase i, (V002.cnt G i + V002.cnt G j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj =>
        three_mul_card_inter_le G hG (Ne.symm (Finset.ne_of_mem_erase hj))
    have hk : k + 2 - 1 = k + 1 := by omega
    have h3 : ∑ j ∈ Finset.univ.erase i, (V002.cnt G i + V002.cnt G j)
        = (k + 1) * V002.cnt G i + ∑ j ∈ Finset.univ.erase i, V002.cnt G j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, hk]
    have h4 : (∑ j ∈ Finset.univ.erase i, V002.cnt G j) + V002.cnt G i
        = ∑ j : Fin (k + 2), V002.cnt G j := Finset.sum_erase_add _ _ (Finset.mem_univ i)
    rw [h1]
    omega
  have htot : 3 * ∑ x : Fin (k + 2) → Bool, G.degree x * G.degree x
      ≤ (2 * k + 5) * (2 * #G.edgeFinset) := by
    rw [V004.sum_sq_degree G hle, Finset.mul_sum]
    calc ∑ i : Fin (k + 2), 3 * ∑ j : Fin (k + 2), #(V002.A G i ∩ V002.A G j)
        ≤ ∑ i : Fin (k + 2),
            (2 * V002.cnt G i + ((k + 1) * V002.cnt G i + ∑ j : Fin (k + 2), V002.cnt G j)) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (2 * k + 5) * (2 * #G.edgeFinset) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hE]
          ring
  have hcard : Fintype.card (Fin (k + 2) → Bool) = 4 * 2 ^ k := by
    simp [pow_add]; ring
  have hdeg : ∑ x : Fin (k + 2) → Bool, G.degree x = 2 * #G.edgeFinset :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hCS : (2 * #G.edgeFinset) * (2 * #G.edgeFinset)
      ≤ (4 * 2 ^ k) * ∑ x : Fin (k + 2) → Bool, G.degree x * G.degree x := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (k + 2) → Bool)))
      (f := fun x => G.degree x)
    simp only [sq] at h
    rwa [Finset.card_univ, hcard, hdeg] at h
  set m := #G.edgeFinset with hm
  clear_value m
  have hkey : 3 * ((2 * m) * (2 * m)) ≤ (4 * 2 ^ k) * ((2 * k + 5) * (2 * m)) := by
    calc 3 * ((2 * m) * (2 * m))
        ≤ 3 * ((4 * 2 ^ k) * ∑ x : Fin (k + 2) → Bool, G.degree x * G.degree x) :=
          Nat.mul_le_mul_left _ hCS
      _ = (4 * 2 ^ k) * (3 * ∑ x : Fin (k + 2) → Bool, G.degree x * G.degree x) := by ring
      _ ≤ (4 * 2 ^ k) * ((2 * k + 5) * (2 * m)) := Nat.mul_le_mul_left _ htot
  have hpow : (2 : ℕ) ^ (k + 2 - 1) = 2 * 2 ^ k := by
    show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k
    rw [pow_succ]; ring
  rw [hpow]
  rcases Nat.eq_zero_or_pos m with rfl | hmp
  · simp
  · have h12 : (12 * m) * m ≤ (2 ^ k * (16 * k + 40)) * m := by nlinarith [hkey]
    have h : 12 * m ≤ 2 ^ k * (16 * k + 40) := Nat.le_of_mul_le_mul_right h12 hmp
    have h4 : 4 * (3 * m) ≤ 4 * (2 ^ k * (4 * k + 10)) := by
      calc 4 * (3 * m) = 12 * m := by ring
        _ ≤ 2 ^ k * (16 * k + 40) := h
        _ = 4 * (2 ^ k * (4 * k + 10)) := by ring
    calc 3 * m ≤ 2 ^ k * (4 * k + 10) := Nat.le_of_mul_le_mul_left h4 (by norm_num)
      _ = (2 * (k + 2) + 1) * (2 * 2 ^ k) := by ring

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f v := by
  intro n
  by_cases hn : 2 ≤ n
  · refine f_le_of_forall_not_hasSquare (by rw [nMin_eq]; omega) fun G _ hle hG => ?_
    exact Nat.le_div_iff_mul_le (by norm_num) |>.mpr
      (by rw [Nat.mul_comm]; exact main hn G hle hG)
  · refine (V004.valid n).trans ?_
    interval_cases n <;> decide

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.minWith_valid V004.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V004.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V004.record record :=
  SqueezeBench.minWith_strict (n₀ := 5) (by decide) (by decide)

end SqueezeBench.HypercubeC4.Upper.V005
