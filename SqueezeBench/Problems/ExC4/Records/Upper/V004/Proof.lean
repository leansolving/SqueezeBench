import SqueezeBench.Problems.ExC4.Records.Upper.V004.Def
import SqueezeBench.Problems.ExC4.Records.Upper.V003.Proof

/-! Record V004 for ExC4, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Upper/V004.lean`. -/

namespace SqueezeBench.ExC4.Upper.V004

open Finset SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

-- The neighbours of `v` that are not neighbours of `x`.
def aset (x v : Fin n) : Finset (Fin n) := G.neighborFinset v \ G.neighborFinset x

-- The vertices that are not neighbours of `x`; `x` itself is one of them.
def sset (x : Fin n) : Finset (Fin n) := univ \ G.neighborFinset x

theorem mem_aset {x v y : Fin n} : y ∈ aset G x v ↔ G.Adj v y ∧ ¬ G.Adj x y := by
  simp [aset]

theorem card_sset (x : Fin n) : #(sset G x) = n - G.degree x := by
  rw [sset, Finset.card_univ_sdiff, Fintype.card_fin, card_neighborFinset_eq_degree]

theorem aset_subset (x v : Fin n) : aset G x v ⊆ sset G x := by
  intro y hy
  rw [mem_aset] at hy
  simp [sset, hy.2]

-- The ordered pairs of distinct vertices of `aset x v`, over `v`, are pairwise disjoint: a pair in
-- two of them would be a pair of vertices with two common neighbours.
theorem aset_offDiag_disjoint (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (x : Fin n)
    {v w : Fin n} (hvw : v ≠ w) : Disjoint (aset G x v).offDiag (aset G x w).offDiag := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [Finset.mem_offDiag, mem_aset, mem_aset] at hp hq
  exact hG v w p.1 p.2 hvw hp.2.2 hp.1.1 hq.1.1 hp.2.1.1 hq.2.1.1

-- The restricted cherry count: `Σ_v a_v(a_v − 1) ≤ s(s − 1)` with `s = n − d(x)`.
theorem sum_aset_le (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (x : Fin n) :
    ∑ v : Fin n, (#(aset G x v) * #(aset G x v) - #(aset G x v))
      ≤ (n - G.degree x) * (n - G.degree x) - (n - G.degree x) := by
  have hsub : (univ : Finset (Fin n)).biUnion (fun v => (aset G x v).offDiag)
      ⊆ (sset G x).offDiag := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, -, hv⟩ := hp
    rw [Finset.mem_offDiag] at hv ⊢
    exact ⟨aset_subset G x v hv.1, aset_subset G x v hv.2.1, hv.2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion (fun v _ w _ h => aset_offDiag_disjoint G hG x h)] at hcard
  simp only [Finset.offDiag_card, card_sset] at hcard
  exact hcard

-- A vertex other than `x` has at most one neighbour in `N(x)`.
theorem degree_le_aset (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {x v : Fin n}
    (hvx : v ≠ x) : G.degree v ≤ #(aset G x v) + 1 := by
  have h1 : #(G.neighborFinset v ∩ G.neighborFinset x) ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at ha hb
    by_contra hab
    exact hG v x a b hvx hab ha.1 ha.2 hb.1 hb.2
  have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset v) (G.neighborFinset x)
  rw [← card_neighborFinset_eq_degree]
  unfold aset
  omega

-- The chord of `a(a − 1)` between `p` and `p + 1`, in subtraction-free form: `(a−p)² ≥ a−p`.
theorem chord (a p : ℕ) : 2 * p * a + a ≤ a * a + p * (p + 1) := by
  rcases le_or_gt a p with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith [Nat.zero_le c, Nat.zero_le (c * c)]
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
    nlinarith [Nat.zero_le c, Nat.zero_le (c * c)]

theorem chord' (a p : ℕ) : 2 * p * a ≤ (a * a - a) + p * (p + 1) := by
  have := chord a p
  have := Nat.le_mul_self a
  omega

-- `4pm ≤ 2p·d(x) + (n − 1)p(p + 3) + (n − d(x))(n − d(x) − 1)` for every vertex `x`.
theorem key (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (x : Fin n) (p : ℕ) :
    4 * p * #G.edgeFinset
      ≤ 2 * p * G.degree x + (n - 1) * (p * (p + 3))
        + (n - G.degree x) * (n - G.degree x - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, #G.edgeFinset = m := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, G.degree x = D := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, ∑ v ∈ univ.erase x, #(aset G x v) = A := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, (n - D) * (n - D) - (n - D) = T := ⟨_, rfl⟩
  have hn1 : #(univ.erase x) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  have hdeg : ∑ v : Fin n, G.degree v = 2 * m := by
    rw [← hm]; exact G.sum_degrees_eq_twice_card_edges
  have hsplit : D + ∑ v ∈ univ.erase x, G.degree v = 2 * m := by
    rw [← hdeg, ← hD]; exact Finset.add_sum_erase univ (fun v => G.degree v) (Finset.mem_univ x)
  have h1 : ∑ v ∈ univ.erase x, G.degree v ≤ A + (n - 1) := by
    calc ∑ v ∈ univ.erase x, G.degree v
        ≤ ∑ v ∈ univ.erase x, (#(aset G x v) + 1) :=
          Finset.sum_le_sum fun v hv => degree_le_aset G hG (Finset.ne_of_mem_erase hv)
      _ = A + (n - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, hn1, smul_eq_mul, mul_one, hA]
  have h2 : 2 * p * A ≤ T + (n - 1) * (p * (p + 1)) := by
    calc 2 * p * A = ∑ v ∈ univ.erase x, 2 * p * #(aset G x v) := by rw [← hA, Finset.mul_sum]
      _ ≤ ∑ v ∈ univ.erase x,
            ((#(aset G x v) * #(aset G x v) - #(aset G x v)) + p * (p + 1)) :=
          Finset.sum_le_sum fun v _ => chord' _ p
      _ = (∑ v ∈ univ.erase x, (#(aset G x v) * #(aset G x v) - #(aset G x v)))
            + (n - 1) * (p * (p + 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, hn1, smul_eq_mul]
      _ ≤ (∑ v : Fin n, (#(aset G x v) * #(aset G x v) - #(aset G x v)))
            + (n - 1) * (p * (p + 1)) :=
          Nat.add_le_add_right
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset x univ)
              (fun _ _ _ => Nat.zero_le _)) _
      _ ≤ T + (n - 1) * (p * (p + 1)) := by
          have := sum_aset_le G hG x
          rw [hD, hT] at this
          exact Nat.add_le_add_right this _
  have hT' : (n - D) * (n - D - 1) = T := by rw [← hT, Nat.mul_sub_one]
  rw [hm, hD, hT']
  have h3 : 2 * p * (2 * m) ≤ 2 * p * (A + (n - 1) + D) := Nat.mul_le_mul_left _ (by omega)
  have e1 : 2 * p * (A + (n - 1) + D) = 2 * p * A + 2 * p * (n - 1) + 2 * p * D := by ring
  have e2 : (n - 1) * (p * (p + 3)) = (n - 1) * (p * (p + 1)) + 2 * p * (n - 1) := by ring
  have e3 : 4 * p * m = 2 * p * (2 * m) := by ring
  omega

theorem edges_le_bp (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (x : Fin n) {p : ℕ}
    (hp : 1 ≤ p) : #G.edgeFinset ≤ bp n (G.degree x) p := by
  rw [bp, Nat.le_div_iff_mul_le (by omega)]
  calc #G.edgeFinset * (4 * p) = 4 * p * #G.edgeFinset := by ring
    _ ≤ _ := key G hG x p

theorem edges_le_half {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) : #G.edgeFinset ≤ n * Δ / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have hdeg : ∑ v : Fin n, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
  have := Finset.sum_le_sum fun v (_ : v ∈ (univ : Finset (Fin n))) => hΔ v
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

theorem cand_le_scanMax (n p : ℕ) {k K : ℕ} (hk : k < K) : cand n k p ≤ scanMax n p K := by
  induction K with
  | zero => omega
  | succ K ih =>
      rw [scanMax]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact le_trans (ih h) (le_max_left _ _)
      · exact le_max_right _ _

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
      obtain ⟨x, -, hx⟩ :=
        Finset.exists_max_image (univ : Finset (Fin (k + 1))) (fun v => G.degree v) univ_nonempty
      have hΔ : G.degree x < k + 1 := by
        have := G.degree_lt_card_verts x
        simpa using this
      have hp : 1 ≤ pOf (k + 1) := le_max_left _ _
      calc #G.edgeFinset ≤ cand (k + 1) (G.degree x) (pOf (k + 1)) :=
            le_min (edges_le_half G fun v => hx v (Finset.mem_univ v)) (edges_le_bp G hG x hp)
        _ ≤ scanMax (k + 1) (pOf (k + 1)) (k + 1) := cand_le_scanMax _ _ hΔ
        _ = v (k + 1) := rfl

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExC4.Upper.V003.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V003.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V003.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 27) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Upper.V004
