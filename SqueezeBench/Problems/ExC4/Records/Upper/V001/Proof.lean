import SqueezeBench.Problems.ExC4.Records.Upper.V001.Def
import SqueezeBench.Problems.ExC4.Records.Upper.V000.Proof

/-! Record V001 for ExC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Upper/V001.lean`. -/

namespace SqueezeBench.ExC4.Upper.V001

open Finset SimpleGraph

/-! ### The integer square root of `Def.lean` never undershoots -/

-- One Newton step stays above `Nat.sqrt x`: `g + x/g ≥ 2√x` by AM-GM.
theorem sqrt_le_sqrtStep (x g : ℕ) (h : Nat.sqrt x ≤ g) : Nat.sqrt x ≤ sqrtStep x g := by
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have : Nat.sqrt x = 0 := Nat.le_zero.mp h
    simp [sqrtStep, this]
  · refine le_min h ?_
    have hsx : Nat.sqrt x * Nat.sqrt x ≤ x := Nat.sqrt_le x
    have key : 2 * Nat.sqrt x - g ≤ x / g := by
      rw [Nat.le_div_iff_mul_le hg]
      rcases le_or_gt (2 * Nat.sqrt x) g with h1 | h1
      · simp [Nat.sub_eq_zero_of_le h1]
      · obtain ⟨d, hd⟩ : ∃ d, 2 * Nat.sqrt x - g = d := ⟨_, rfl⟩
        have hdg : d + g = 2 * Nat.sqrt x := by omega
        rw [hd]
        nlinarith [two_mul_le_add_sq d g, hdg, hsx]
    obtain ⟨q, hq⟩ : ∃ q, x / g = q := ⟨_, rfl⟩
    rw [hq] at key
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2), hq]
    omega

theorem sqrt_le_sqrtIter (k x g : ℕ) (h : Nat.sqrt x ≤ g) : Nat.sqrt x ≤ sqrtIter k x g := by
  induction k generalizing g with
  | zero => simpa [sqrtIter] using h
  | succ k ih =>
      rw [sqrtIter]
      exact ih _ (sqrt_le_sqrtStep x g h)

theorem sqrt_le_isqrt (x : ℕ) : Nat.sqrt x ≤ isqrt x :=
  sqrt_le_sqrtIter 64 x (x + 1) (le_trans (Nat.sqrt_le_self x) (Nat.le_succ x))

/-! ### Counting cherries -/

-- `d² = 2·C(d,2) + d`, the identity that turns the cherry count into a sum of squares.
theorem mul_self_eq (d : ℕ) : d * d = 2 * d.choose 2 + d := by
  induction d with
  | zero => rfl
  | succ e ih =>
      have h1 : (e + 1).choose 2 = e + e.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have h2 : (e + 1) * (e + 1) = e * e + 2 * e + 1 := by ring
      rw [h1, h2, ih]; ring

-- Each pair of distinct vertices is the pair of ends of at most one cherry, so the 2-element
-- subsets of the neighbourhoods are pairwise disjoint and all lie in the 2-subsets of `Fin n`.
theorem sum_choose_degree_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) :
    ∑ x : Fin n, (G.degree x).choose 2 ≤ n.choose 2 := by
  have hdisj : ∀ x ∈ (univ : Finset (Fin n)), ∀ y ∈ (univ : Finset (Fin n)), x ≠ y →
      Disjoint ((G.neighborFinset x).powersetCard 2) ((G.neighborFinset y).powersetCard 2) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro s hsx hsy
    rw [Finset.mem_powersetCard] at hsx hsy
    obtain ⟨u, w, huw, hs⟩ := Finset.card_eq_two.mp hsx.2
    subst hs
    have hu : u ∈ ({u, w} : Finset (Fin n)) := by simp
    have hw : w ∈ ({u, w} : Finset (Fin n)) := by simp
    exact hG x y u w hxy huw
      (by simpa using hsx.1 hu) (by simpa using hsy.1 hu)
      (by simpa using hsx.1 hw) (by simpa using hsy.1 hw)
  calc ∑ x : Fin n, (G.degree x).choose 2
      = ∑ x : Fin n, #((G.neighborFinset x).powersetCard 2) := by
        simp [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
    _ = #(univ.biUnion fun x : Fin n => (G.neighborFinset x).powersetCard 2) :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ #((univ : Finset (Fin n)).powersetCard 2) := by
        refine Finset.card_le_card ?_
        intro s hs
        rw [Finset.mem_biUnion] at hs
        obtain ⟨x, -, hx⟩ := hs
        rw [Finset.mem_powersetCard] at hx ⊢
        exact ⟨Finset.subset_univ s, hx.2⟩
    _ = n.choose 2 := by simp [Finset.card_powersetCard]

/-! ### Reiman's bound -/

-- `4m² ≤ n²(n−1) + 2mn` forces `4m ≤ n + √(n²(4n−3))`, by completing the square.
theorem reiman_arith {k m : ℕ}
    (h : 4 * (m * m) ≤ (k + 1) * ((k + 1) * k) + 2 * ((k + 1) * m)) :
    4 * m ≤ (k + 1) + Nat.sqrt ((k + 1) * (k + 1) * (4 * (k + 1) - 3)) := by
  have hS : 4 * (k + 1) - 3 = 4 * k + 1 := by omega
  rw [hS]
  rcases le_or_gt (4 * m) (k + 1) with hc | hc
  · omega
  · obtain ⟨t, hteq⟩ : ∃ t, 4 * m - (k + 1) = t := ⟨_, rfl⟩
    have ht : t + (k + 1) = 4 * m := by omega
    have hkey : t * t ≤ (k + 1) * (k + 1) * (4 * k + 1) := by nlinarith [h, ht]
    have := Nat.le_sqrt.mpr hkey
    omega

theorem card_edgeFinset_le {k : ℕ} (G : SimpleGraph (Fin (k + 1))) [DecidableRel G.Adj]
    (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) : #G.edgeFinset ≤ v (k + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, #G.edgeFinset = m := ⟨_, rfl⟩
  have hdeg : ∑ x : Fin (k + 1), G.degree x = 2 * m := by
    rw [← hm]; exact G.sum_degrees_eq_twice_card_edges
  have hsq : ∑ x : Fin (k + 1), G.degree x * G.degree x
      = 2 * (∑ x : Fin (k + 1), (G.degree x).choose 2) + 2 * m := by
    rw [← hdeg, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => mul_self_eq _
  have hcs : (∑ x : Fin (k + 1), G.degree x) ^ 2
      ≤ (k + 1) * ∑ x : Fin (k + 1), G.degree x ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (k + 1))))
      (f := fun x => G.degree x)
  have hchoose : 2 * (k + 1).choose 2 = (k + 1) * k := by
    have h1 := mul_self_eq (k + 1)
    have h2 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    omega
  have hkey : 4 * (m * m) ≤ (k + 1) * ((k + 1) * k) + 2 * ((k + 1) * m) := by
    have hb : ∑ x : Fin (k + 1), G.degree x * G.degree x ≤ (k + 1) * k + 2 * m := by
      rw [hsq, ← hchoose]
      have := sum_choose_degree_le G hG
      omega
    have hcs' : 2 * m * (2 * m) ≤ (k + 1) * ((k + 1) * k + 2 * m) := by
      calc 2 * m * (2 * m) = (∑ x : Fin (k + 1), G.degree x) ^ 2 := by rw [hdeg]; ring
        _ ≤ (k + 1) * ∑ x : Fin (k + 1), G.degree x ^ 2 := hcs
        _ = (k + 1) * ∑ x : Fin (k + 1), G.degree x * G.degree x := by
              simp [pow_two]
        _ ≤ (k + 1) * ((k + 1) * k + 2 * m) := Nat.mul_le_mul_left _ hb
    nlinarith [hcs']
  rw [hm]
  have := reiman_arith hkey
  have hsq' := sqrt_le_isqrt ((k + 1) * (k + 1) * (4 * (k + 1) - 3))
  rw [v, Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
  omega

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f v := by
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
      exact card_edgeFinset_le G hG

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExC4.Upper.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V000.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V000.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 10) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Upper.V001
