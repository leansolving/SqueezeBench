import SqueezeBench.Problems.HypercubeC4.Records.Upper.V006.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V005.Proof

/-! Record V006 for HypercubeC4, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V006.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V006

open Finset SimpleGraph

/-! ## Flip algebra -/

theorem opp_comm {n : ℕ} (x : Fin n → Bool) (a b : Fin n) : V002.opp x a b = V002.opp x b a :=
  V005.flip_comm x a b

theorem opp_opp_left {n : ℕ} (x : Fin n → Bool) (a b c : Fin n) :
    V002.opp (V002.opp x a b) a c = V002.opp x b c := by
  simp only [V002.opp]
  rw [V005.flip_comm (flip x a) b a, flip_flip]

theorem opp_opp_right {n : ℕ} (x : Fin n → Bool) (a b c : Fin n) :
    V002.opp (V002.opp x a b) b c = V002.opp x a c := by
  simp only [V002.opp, flip_flip]

/-! ## Involutions -/

theorem card_union_image_involution {n : ℕ} (σ : (Fin n → Bool) → (Fin n → Bool))
    (hσ : ∀ x, σ (σ x) = x) (U : Finset (Fin n → Bool)) (hU : ∀ x ∈ U, σ x ∉ U) :
    #(U ∪ U.image σ) = 2 * #U := by
  have hinj : Set.InjOn σ ↑U := fun a _ b _ hab => by
    have := congrArg σ hab
    simpa [hσ] using this
  have hdisj : Disjoint U (U.image σ) := by
    rw [Finset.disjoint_right]
    intro y hy hyU
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hU x hx hyU
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
  ring

theorem two_mul_card_le_of_involution {n : ℕ} (σ : (Fin n → Bool) → (Fin n → Bool))
    (hσ : ∀ x, σ (σ x) = x) (U : Finset (Fin n → Bool)) (hU : ∀ x ∈ U, σ x ∉ U) :
    2 * #U ≤ 2 ^ n := by
  have h := card_union_image_involution σ hσ U hU
  have h2 : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have h3 := Finset.card_le_univ (U ∪ U.image σ)
  omega

/-! ## At most two corners of a `Q₃` block carry all three edges -/

theorem card_triple_le {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    4 * #(V002.A G i ∩ V002.A G j ∩ V002.A G k) ≤ 2 ^ n := by
  set S := V002.A G i ∩ V002.A G j ∩ V002.A G k with hS
  have key_ij : ∀ x ∈ S, V002.opp x i j ∉ S := fun x hx h =>
    V005.opp_not_mem G hG hij (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp h).1
  have key_ik : ∀ x ∈ S, V002.opp x i k ∉ S := fun x hx h =>
    V005.opp_not_mem G hG hik
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
        (Finset.mem_inter.mp hx).2⟩)
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1,
        (Finset.mem_inter.mp h).2⟩)
  have key_jk : ∀ x ∈ S, V002.opp x j k ∉ S := fun x hx h =>
    V005.opp_not_mem G hG hjk
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩)
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2,
        (Finset.mem_inter.mp h).2⟩)
  set U := S ∪ S.image (fun x => V002.opp x i j) with hUdef
  have hU : #U = 2 * #S :=
    card_union_image_involution _ (fun x => V002.opp_opp x hij) S key_ij
  have hU2 : ∀ y ∈ U, V002.opp y i k ∉ U := by
    intro y hy hy'
    simp only [hUdef, Finset.mem_union, Finset.mem_image] at hy hy'
    rcases hy with hy | ⟨x, hx, rfl⟩ <;> rcases hy' with hy' | ⟨z, hz, hz'⟩
    · exact key_ik y hy hy'
    · have hz2 : z = V002.opp y j k := by
        have := congrArg (fun w => V002.opp w i j) hz'
        simp only [V002.opp_opp _ hij] at this
        rw [this, opp_opp_left, opp_comm]
      exact key_jk y hy (hz2 ▸ hz)
    · rw [opp_opp_left] at hy'
      exact key_jk x hx hy'
    · rw [opp_opp_left] at hz'
      have hz2 : z = V002.opp x i k := by
        have := congrArg (fun w => V002.opp w i j) hz'
        simp only [V002.opp_opp _ hij] at this
        rw [this, opp_comm _ i j, opp_opp_left, opp_comm]
      exact key_ik x hx (hz2 ▸ hz)
  have := two_mul_card_le_of_involution _ (fun x => V002.opp_opp x hik) U hU2
  omega


/-! ## The third moment of the degrees -/

-- The directions of the edges of `G` at `x`.
def dirs {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => G.Adj x (flip x i))

theorem mem_dirs {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (i : Fin n) : i ∈ dirs G x ↔ G.Adj x (flip x i) := by
  simp [dirs]

theorem choose_three_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    (#(dirs G x)).choose 3
      = #((powersetCard 3 (Finset.univ : Finset (Fin n))).filter (fun T => T ⊆ dirs G x)) := by
  rw [← Finset.card_powersetCard]
  congr 1
  ext T
  simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
  tauto

theorem sum_choose_three_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] :
    ∑ x : Fin n → Bool, (#(dirs G x)).choose 3
      = ∑ T ∈ powersetCard 3 (Finset.univ : Finset (Fin n)),
          #(Finset.univ.filter (fun x => T ⊆ dirs G x)) := by
  simp only [choose_three_eq, Finset.card_filter]
  exact Finset.sum_comm

theorem card_filter_subset_le {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) (T : Finset (Fin n)) (hT : T ∈ powersetCard 3 (Finset.univ : Finset (Fin n))) :
    4 * #(Finset.univ.filter (fun x => T ⊆ dirs G x)) ≤ 2 ^ n := by
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hT.2
  have h : Finset.univ.filter (fun x => ({i, j, k} : Finset (Fin n)) ⊆ dirs G x)
      = V002.A G i ∩ V002.A G j ∩ V002.A G k := by
    ext x
    simp [Finset.insert_subset_iff, mem_dirs, V002.A]
  rw [h]
  exact card_triple_le G hG hij hik hjk

theorem sum_choose_three_le {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) :
    ∑ x : Fin n → Bool, (G.degree x).choose 3 ≤ n.choose 3 * 2 ^ (n - 2) := by
  have hdeg : ∀ x, G.degree x = #(dirs G x) := fun x => V002.degree_eq' G hle x
  simp only [hdeg]
  rw [sum_choose_three_eq]
  have hpow : 2 ^ n = 4 * 2 ^ (n - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]; ring
  calc ∑ T ∈ powersetCard 3 (Finset.univ : Finset (Fin n)),
          #(Finset.univ.filter (fun x => T ⊆ dirs G x))
      ≤ ∑ _T ∈ powersetCard 3 (Finset.univ : Finset (Fin n)), 2 ^ (n - 2) :=
        Finset.sum_le_sum fun T hT => by
          have h := card_filter_subset_le G hG T hT
          omega
    _ = n.choose 3 * 2 ^ (n - 2) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

/-! ## Convexity of `C(·, 3)` -/

-- The secant of `C(·, 3)` at `c`, of slope `C(c, 2)`, lies below `C(·, 3)`.
theorem choose_three_secant (c d : ℕ) :
    c.choose 3 + c.choose 2 * d ≤ c.choose 2 * c + d.choose 3 := by
  rcases le_or_gt c d with hcd | hdc
  · induction d, hcd using Nat.le_induction with
    | base => omega
    | succ d hcd ih =>
      have h1 : (d + 1).choose 3 = d.choose 2 + d.choose 3 := Nat.choose_succ_succ' d 2
      have h2 : c.choose 2 ≤ d.choose 2 := Nat.choose_le_choose 2 hcd
      rw [h1, Nat.mul_succ]
      omega
  · obtain ⟨e, rfl⟩ : ∃ e, c = d + e + 1 := ⟨c - d - 1, by omega⟩
    induction e generalizing d with
    | zero =>
      have h1 : (d + 0 + 1).choose 3 = d.choose 2 + d.choose 3 := Nat.choose_succ_succ' d 2
      have h2 : d.choose 2 ≤ (d + 0 + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
      rw [h1, Nat.mul_succ]
      omega
    | succ e ih =>
      have h := ih (d + 1) (by omega)
      have h1 : (d + 1).choose 3 = d.choose 2 + d.choose 3 := Nat.choose_succ_succ' d 2
      have h2 : d.choose 2 ≤ (d + (e + 1) + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
      have h3 : d + 1 + e + 1 = d + (e + 1) + 1 := by ring
      rw [h3, h1, Nat.mul_succ] at h
      omega

theorem jensen_sum {n : ℕ} (c : ℕ) (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] :
    2 ^ n * c.choose 3 + c.choose 2 * (2 * #G.edgeFinset)
      ≤ 2 ^ n * (c.choose 2 * c) + ∑ x : Fin n → Bool, (G.degree x).choose 3 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool)))
    fun x _ => choose_three_secant c (G.degree x)
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    ← Finset.mul_sum, Finset.card_univ, hcard, smul_eq_mul, smul_eq_mul,
    SimpleGraph.sum_degrees_eq_twice_card_edges] at h
  exact h

-- `2 · C(m+1, 2) = (m+1) · m`.
theorem two_mul_choose_two (m : ℕ) : 2 * (m + 1).choose 2 = (m + 1) * m := by
  have h := Nat.add_one_mul_choose_eq m 1
  rw [Nat.choose_one_right] at h
  norm_num at h
  omega

-- `6 · C(m+2, 3) = (m+2)(m+1)m`.
theorem six_mul_choose_three (m : ℕ) : 6 * (m + 2).choose 3 = (m + 2) * (m + 1) * m := by
  have h := Nat.add_one_mul_choose_eq (m + 1) 2
  have h2 := two_mul_choose_two m
  norm_num at h
  nlinarith

/-! ## The bound -/

theorem main {n : ℕ} (hn : 3 ≤ n) {c : ℕ} (hc : 2 ≤ c) (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) :
    #G.edgeFinset ≤ bound n c := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, c = b + 2 := ⟨c - 2, by omega⟩
  have hS := sum_choose_three_le (by omega) G hle hG
  have hJ := jensen_sum (b + 2) G
  set m := #G.edgeFinset with hm
  set S3 := ∑ x : Fin (k + 3) → Bool, (G.degree x).choose 3 with hS3
  clear_value m S3
  have h2 : 2 * (b + 2).choose 2 = (b + 2) * (b + 1) := two_mul_choose_two (b + 1)
  have h3 : 6 * (b + 2).choose 3 = (b + 2) * (b + 1) * b := six_mul_choose_three b
  have h4 : 6 * (k + 3).choose 3 = (k + 3) * (k + 2) * (k + 1) := six_mul_choose_three (k + 1)
  have hpow : (2 : ℕ) ^ (k + 3) = 4 * 2 ^ (k + 1) := by rw [pow_add, pow_add]; ring
  have he1 : k + 3 - 2 = k + 1 := by omega
  have he2 : k + 3 - 1 = k + 2 := by omega
  have he3 : b + 2 - 1 = b + 1 := by omega
  rw [he1] at hS
  rw [hpow] at hJ
  simp only [bound, he1, he2, he3]
  rw [Nat.le_div_iff_mul_le (by positivity)]
  set A := (b + 2).choose 2 with hA
  set B := (b + 2).choose 3 with hB
  set C := (k + 3).choose 3 with hC
  set T := (2 : ℕ) ^ (k + 1) with hT
  clear_value A B C T
  have hAm : (2 * A) * m = ((b + 2) * (b + 1)) * m := by rw [h2]
  have hAT : (2 * A) * T = ((b + 2) * (b + 1)) * T := by rw [h2]
  have hATb : (2 * A) * (T * b) = ((b + 2) * (b + 1)) * (T * b) := by rw [h2]
  have hBT : (6 * B) * T = ((b + 2) * (b + 1) * b) * T := by rw [h3]
  have hCT : (6 * C) * T = ((k + 3) * (k + 2) * (k + 1)) * T := by rw [h4]
  linarith [hS, hJ, hAm, hAT, hATb, hBT, hCT]

-- Each `bound n c` with `c ≥ 2` is a bound, so their minimum is.
theorem le_best {n X : ℕ} (h : ∀ c, 2 ≤ c → X ≤ bound n c) : ∀ k, X ≤ best n k
  | 0 => h 2 le_rfl
  | k + 1 => le_min (le_best h k) (h (k + 3) (by omega))

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f v := by
  intro n
  by_cases hn : 3 ≤ n
  · refine f_le_of_forall_not_hasSquare (by rw [nMin_eq]; omega) fun G _ hle hG => ?_
    exact le_best (fun c hc => main hn hc G hle hG) n
  · refine (V005.valid n).trans ?_
    interval_cases n <;> decide

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.minWith_valid SqueezeBench.HypercubeC4.Upper.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V005.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V005.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.HypercubeC4.nMin) (n₀ := 7) (by decide) (by decide)

end SqueezeBench.HypercubeC4.Upper.V006
