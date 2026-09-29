import SqueezeBench.Problems.HypercubeC4.Records.Upper.V004.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V003.Proof

/-! Record V004 for HypercubeC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V004.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V004

open Finset SimpleGraph

/-! ## The integer square root -/

-- `4xy ≤ (x + y)²`.
theorem four_mul_le_sq_add (x y : ℕ) : 4 * (x * y) ≤ (x + y) * (x + y) := by
  have h : (4 * (x * y) : ℤ) ≤ ((x : ℤ) + y) * ((x : ℤ) + y) := by nlinarith [sq_nonneg ((x : ℤ) - y)]
  exact_mod_cast h

-- A Newton step from any positive guess stays above every `d` with `d² ≤ a`.
theorem le_step {a g d : ℕ} (hg : 0 < g) (hd : d * d ≤ a) : d ≤ step a g := by
  have hka : a < (a / g + 1) * g := by
    have h1 := Nat.div_add_mod a g
    have h2 : a % g < g := Nat.mod_lt _ hg
    calc a = g * (a / g) + a % g := h1.symm
      _ < g * (a / g) + g := Nat.add_lt_add_left h2 _
      _ = (a / g + 1) * g := by ring
  by_contra hlt
  push_neg at hlt
  rw [step, Nat.div_lt_iff_lt_mul (by norm_num)] at hlt
  set q := a / g with hq
  have hle : (q + 1) + g ≤ 2 * d := by omega
  have h4 : 4 * ((q + 1) * g) ≤ 4 * (d * d) := by
    calc 4 * ((q + 1) * g) ≤ ((q + 1) + g) * ((q + 1) + g) := four_mul_le_sq_add _ _
      _ ≤ (2 * d) * (2 * d) := Nat.mul_le_mul hle hle
      _ = 4 * (d * d) := by ring
  have hfin : (q + 1) * g ≤ d * d := Nat.le_of_mul_le_mul_left h4 (by norm_num)
  exact absurd hka (Nat.not_lt.mpr (hfin.trans hd))

-- A positive guess stays positive.
theorem step_pos {a g : ℕ} (ha : 0 < a) (hg : 0 < g) : 0 < step a g := by
  have h2 : 2 ≤ g + a / g := by
    rcases le_or_gt g a with h | h
    · have h1 : 1 ≤ a / g := (Nat.one_le_div_iff hg).mpr h
      omega
    · exact le_trans (by omega) (Nat.le_add_right g _)
  exact (Nat.one_le_div_iff (by norm_num)).mpr h2

theorem le_iter {a d : ℕ} (ha : 0 < a) (hd : d * d ≤ a) :
    ∀ (k g : ℕ), 0 < g → d ≤ g → d ≤ iter k a g := by
  intro k
  induction k with
  | zero => intro g _ hdg; simpa [iter] using hdg
  | succ k ih =>
    intro g hg hdg
    rw [iter]
    split
    · exact ih (step a g) (step_pos ha hg) (le_step hg hd)
    · exact hdg

theorem le_isqrt {fuel a d : ℕ} (hd : d * d ≤ a) : d ≤ isqrt fuel a := by
  rcases Nat.eq_zero_or_pos d with rfl | hdp
  · exact Nat.zero_le _
  · have ha : 0 < a := lt_of_lt_of_le hdp (le_trans (Nat.le_mul_of_pos_left d hdp) hd)
    exact le_iter ha hd fuel a ha (le_trans (Nat.le_mul_of_pos_left d hdp) hd)

/-! ## The double count -/

-- `A G i ∩ A G j` fits in half the cube, by the involution of V002.
theorem card_inter_le' {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) :
    #(V002.A G i ∩ V002.A G j) ≤ 2 ^ (n - 1) := by
  have h := V002.card_inter_le G hG hij
  have hp : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; ring_nf
    simp
  omega

theorem degree_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (x : Fin n → Bool) :
    G.degree x = ∑ i : Fin n, (if G.Adj x (flip x i) then 1 else 0) := by
  rw [V002.degree_eq' G hle, Finset.card_filter]

theorem sum_prod_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i j : Fin n) :
    ∑ x : Fin n → Bool,
        (if G.Adj x (flip x i) then 1 else 0) * (if G.Adj x (flip x j) then 1 else 0)
      = #(V002.A G i ∩ V002.A G j) := by
  rw [V002.A, V002.A, ← Finset.filter_and, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : G.Adj x (flip x i) <;> by_cases h2 : G.Adj x (flip x j) <;> simp [h1, h2]

theorem sum_sq_degree {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) :
    ∑ x : Fin n → Bool, G.degree x * G.degree x
      = ∑ i : Fin n, ∑ j : Fin n, #(V002.A G i ∩ V002.A G j) := by
  have h1 : ∀ x : Fin n → Bool, G.degree x * G.degree x
      = ∑ i : Fin n, ∑ j : Fin n,
          (if G.Adj x (flip x i) then 1 else 0) * (if G.Adj x (flip x j) then 1 else 0) := by
    intro x
    rw [degree_eq G hle x, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => sum_prod_eq G i j

theorem row_le {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) (i : Fin n) :
    ∑ j : Fin n, #(V002.A G i ∩ V002.A G j) ≤ V002.cnt G i + (n - 1) * 2 ^ (n - 1) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have h1 : #(V002.A G i ∩ V002.A G i) = V002.cnt G i := by
    rw [Finset.inter_self]; rfl
  have h2 : ∑ j ∈ Finset.univ.erase i, #(V002.A G i ∩ V002.A G j) ≤ (n - 1) * 2 ^ (n - 1) := by
    calc ∑ j ∈ Finset.univ.erase i, #(V002.A G i ∩ V002.A G j)
        ≤ ∑ _j ∈ Finset.univ.erase i, 2 ^ (n - 1) :=
          Finset.sum_le_sum fun j hj =>
            card_inter_le' hn G hG (Ne.symm (Finset.ne_of_mem_erase hj))
      _ = (n - 1) * 2 ^ (n - 1) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  omega

-- `Σ_x deg(x)² ≤ 2·#E + n(n−1)·2ⁿ⁻¹`: no pair of words has two common neighbours.
theorem sum_sq_le {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) :
    ∑ x : Fin n → Bool, G.degree x * G.degree x
      ≤ 2 * #G.edgeFinset + n * ((n - 1) * 2 ^ (n - 1)) := by
  rw [sum_sq_degree G hle]
  calc ∑ i : Fin n, ∑ j : Fin n, #(V002.A G i ∩ V002.A G j)
      ≤ ∑ i : Fin n, (V002.cnt G i + (n - 1) * 2 ^ (n - 1)) :=
        Finset.sum_le_sum fun i _ => row_le hn G hG i
    _ = (∑ i : Fin n, V002.cnt G i) + n * ((n - 1) * 2 ^ (n - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
    _ = 2 * #G.edgeFinset + n * ((n - 1) * 2 ^ (n - 1)) := by
        rw [← V002.two_mul_edges G hle]

/-! ## The bound -/

theorem main {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) : #G.edgeFinset ≤ v n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hcard : Fintype.card (Fin (k + 2) → Bool) = 4 * 2 ^ k := by
    simp [pow_add]; ring
  have hdeg : ∑ x : Fin (k + 2) → Bool, G.degree x = 2 * #G.edgeFinset :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hCS : (∑ x : Fin (k + 2) → Bool, G.degree x) * (∑ x : Fin (k + 2) → Bool, G.degree x)
      ≤ (4 * 2 ^ k) * ∑ x : Fin (k + 2) → Bool, G.degree x * G.degree x := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (k + 2) → Bool)))
      (f := fun x => G.degree x)
    rw [sq] at h
    simp only [sq] at h
    rwa [Finset.card_univ, hcard] at h
  have hsq := sum_sq_le (by omega) G hle hG
  rw [hdeg] at hCS
  have hpow1 : (2 : ℕ) ^ (k + 2 - 1) = 2 * 2 ^ k := by
    show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k
    rw [pow_succ]; ring
  rw [hpow1] at hsq
  -- `4m² ≤ 4·2ᵏ·(2m + (k+2)(k+1)·2·2ᵏ)`
  have hkey : (2 * #G.edgeFinset) * (2 * #G.edgeFinset)
      ≤ (4 * 2 ^ k) * (2 * #G.edgeFinset + (k + 2) * ((k + 1) * (2 * 2 ^ k))) := by
    refine hCS.trans (Nat.mul_le_mul_left _ ?_)
    simpa using hsq
  set t := (2 : ℕ) ^ k with ht
  set m := #G.edgeFinset with hm
  clear_value m
  have hm2 : m * m ≤ 2 * (t * m) + 2 * (t * t) * ((k + 2) * (k + 1)) := by nlinarith [hkey]
  show m ≤ 2 ^ (k + 2 - 2) + isqrt (2 * (k + 2) + 16)
      (2 ^ (k + 2 - 2) * 2 ^ (k + 2 - 2) * (1 + 2 * (k + 2) * (k + 2 - 1)))
  have he1 : k + 2 - 2 = k := by omega
  have he2 : k + 2 - 1 = k + 1 := by omega
  rw [he1, he2, ← ht]
  rcases le_or_gt m t with hmt | hmt
  · exact le_trans hmt (Nat.le_add_right _ _)
  · obtain ⟨d, rfl⟩ : ∃ d, m = t + d := ⟨m - t, by omega⟩
    have hd : d * d ≤ t * t * (1 + 2 * (k + 2) * (k + 1)) := by nlinarith [hm2]
    exact Nat.add_le_add_left (le_isqrt hd) t

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f v := by
  intro n
  by_cases hn : 2 ≤ n
  · exact f_le_of_forall_not_hasSquare (by rw [nMin_eq]; omega) fun G _ hle hG => main hn G hle hG
  · refine (V003.valid n).trans ?_
    interval_cases n <;> decide

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.minWith_valid V003.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V003.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V003.record record :=
  SqueezeBench.minWith_strict (n₀ := 5) (by decide) (by decide)

end SqueezeBench.HypercubeC4.Upper.V004
