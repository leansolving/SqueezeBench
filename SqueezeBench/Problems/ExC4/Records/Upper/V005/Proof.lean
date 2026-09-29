import SqueezeBench.Problems.ExC4.Records.Upper.V005.Def
import SqueezeBench.Problems.ExC4.Records.Upper.V004.Proof

/-! Record V005 for ExC4, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Upper/V005.lean`. -/

namespace SqueezeBench.ExC4.Upper.V005

open Finset SimpleGraph

/-! ### The certificate: (D1) at every degree and (D2) at every pair of positive degrees -/

theorem allFrom_spec {p : ℕ → Bool} {lo c : ℕ} (h : allFrom p lo c = true) :
    ∀ i, lo ≤ i → i < lo + c → p i = true := by
  induction c with
  | zero => intro i h1 h2; omega
  | succ c ih =>
      rw [allFrom, Bool.and_eq_true] at h
      intro i h1 h2
      rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : i - lo < c + 1) with h3 | h3
      · exact ih h.2 i h1 (by omega)
      · have : i = lo + c := by omega
        rw [this]; exact h.1

-- Beyond `T = k + |ls|` the weight is the tail `g` and the offset is linear.
theorem wt_tail (k : ℕ) (ls : List ℕ) (g : ℕ) {i : ℕ} (hi : k + ls.length ≤ i) :
    wt k ls g i = g := by
  rw [wt, if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem dl_tail (n k : ℕ) (ls : List ℕ) (g β : ℕ) {i : ℕ} (hi : k + ls.length ≤ i) :
    dl n k ls g β i = (i - 1) * g - M := by
  rw [dl, if_neg (by omega)]

theorem dl_low (n k : ℕ) (ls : List ℕ) (g β : ℕ) {i : ℕ} (hi : i < k + ls.length) :
    dl n k ls g β i = dlow n β i (wt k ls g i) := by
  rw [dl, if_pos hi]

-- (D1) at a checked degree, from `d1ok` and the floor in `dlow`.
theorem d1_of_ok {n β i w : ℕ} (h : d1ok n β i w = true) :
    M * i + w * (n - 1 - i % 2) + i * dlow n β i w ≤ β + i * (w * (i - 1)) := by
  rw [d1ok, decide_eq_true_eq] at h
  have := Nat.mul_div_le (β + i * (w * (i - 1)) - (M * i + w * (n - 1 - i % 2))) i
  rw [dlow]
  omega

theorem certOk_parts {n k : ℕ} {ls : List ℕ} {B : ℕ} (h : certOk n k ls B = true) :
    M ≤ (k + ls.length - 1) * gOf n B ∧ gOf n B * (n - 1) ≤ betaOf n B
      ∧ wt k ls (gOf n B) 0 * (n - 1) ≤ betaOf n B
      ∧ (∀ i, 1 ≤ i → i < k + ls.length → d1ok n (betaOf n B) i (wt k ls (gOf n B) i) = true)
      ∧ (∀ i j, 1 ≤ i → i < j → j ≤ k + ls.length →
          d2ok n k ls (gOf n B) (betaOf n B) i j = true) := by
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun i hi hiT => allFrom_spec h4 i hi (by omega), fun i j hi hij hjT => ?_⟩
  have := allFrom_spec h5 i hi (by omega)
  exact allFrom_spec this j (by omega) (by omega)

-- (D1) for every degree `i`.
theorem d1_all {n k : ℕ} {ls : List ℕ} {B : ℕ} (h : certOk n k ls B = true) (i : ℕ) :
    M * i + wt k ls (gOf n B) i * (n - 1 - i % 2) + i * dl n k ls (gOf n B) (betaOf n B) i
      ≤ betaOf n B + i * (wt k ls (gOf n B) i * (i - 1)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := certOk_parts h
  rcases Nat.lt_or_ge i (k + ls.length) with hi | hi
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [Nat.mul_zero, Nat.zero_mod, Nat.sub_zero, zero_mul, add_zero, zero_add]
      exact h3
    · rw [dl_low n k ls _ _ hi]
      exact d1_of_ok (h4 i hpos hi)
  · rw [wt_tail k ls _ hi, dl_tail n k ls _ _ hi]
    have hg : M ≤ (i - 1) * gOf n B :=
      le_trans h1 (Nat.mul_le_mul_right _ (by omega))
    have e : i * ((i - 1) * gOf n B - M) + M * i = i * ((i - 1) * gOf n B) := by
      obtain ⟨a, ha⟩ : ∃ a, (i - 1) * gOf n B = M + a := ⟨_, (Nat.add_sub_cancel' hg).symm⟩
      rw [ha, Nat.add_sub_cancel_left, Nat.mul_add, Nat.mul_comm M i]
      omega
    have hpar : gOf n B * (n - 1 - i % 2) ≤ gOf n B * (n - 1) :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have e2 : i * (gOf n B * (i - 1)) = i * ((i - 1) * gOf n B) := by ring
    omega

-- (D2) for every pair of positive degrees.
theorem d2_all {n k : ℕ} {ls : List ℕ} {B : ℕ} (h : certOk n k ls B = true) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    wt k ls (gOf n B) i * (i - 1) + wt k ls (gOf n B) j * (j - 1)
      ≤ wt k ls (gOf n B) i * (j - 1) + wt k ls (gOf n B) j * (i - 1)
        + dl n k ls (gOf n B) (betaOf n B) i + dl n k ls (gOf n B) (betaOf n B) j := by
  obtain ⟨h1, -, -, -, h5⟩ := certOk_parts h
  wlog hij : i ≤ j generalizing i j
  · have := this hj hi (by omega)
    omega
  obtain ⟨T, hT⟩ : ∃ T, k + ls.length = T := ⟨_, rfl⟩
  rw [hT] at h1 h5
  rcases Nat.lt_or_ge j (T + 1) with hjT | hjT
  · rcases Nat.lt_or_ge i j with hlt | hge
    · have := h5 i j hi hlt (by omega)
      rw [d2ok, decide_eq_true_eq] at this
      exact this
    · have : i = j := by omega
      subst this
      omega
  · rcases Nat.lt_or_ge i T with hiT | hiT
    · have hpair := h5 i T hi hiT le_rfl
      rw [d2ok, decide_eq_true_eq] at hpair
      rw [wt_tail k ls _ (le_of_eq hT), dl_tail n k ls _ _ (le_of_eq hT)] at hpair
      rw [wt_tail k ls _ (by omega : k + ls.length ≤ j),
        dl_tail n k ls _ _ (by omega : k + ls.length ≤ j)]
      obtain ⟨t, rfl⟩ : ∃ t, j = T + t := ⟨j - T, by omega⟩
      obtain ⟨a, ha⟩ : ∃ a, (T - 1) * gOf n B = M + a := ⟨_, (Nat.add_sub_cancel' h1).symm⟩
      have hb : (T + t - 1) * gOf n B = M + a + t * gOf n B := by
        have : T + t - 1 = (T - 1) + t := by omega
        rw [this, Nat.add_mul, ha]
      rw [ha, Nat.add_sub_cancel_left] at hpair
      have hc : M + a + t * gOf n B - M = a + t * gOf n B := by omega
      rw [hb, hc]
      have e1 : wt k ls (gOf n B) i * (T + t - 1)
          = wt k ls (gOf n B) i * (T - 1) + wt k ls (gOf n B) i * t := by
        have : T + t - 1 = (T - 1) + t := by omega
        rw [this, Nat.mul_add]
      have e2 : gOf n B * (T + t - 1) = gOf n B * (T - 1) + gOf n B * t := by
        have : T + t - 1 = (T - 1) + t := by omega
        rw [this, Nat.mul_add]
      have e3 : t * gOf n B = gOf n B * t := Nat.mul_comm _ _
      omega
    · rw [wt_tail k ls _ (by omega : k + ls.length ≤ i),
        wt_tail k ls _ (by omega : k + ls.length ≤ j)]
      omega

/-! ### The graph side: the local count at a vertex, and sums over ordered adjacent pairs -/

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

-- `s(x) = Σ_{y ∈ N(x)} (d(y) − 1)`.
def sval (x : Fin n) : ℕ := ∑ y ∈ G.neighborFinset x, (G.degree y - 1)

-- The neighbours of `x` that share no neighbour with `x`.
def lone (x : Fin n) : Finset (Fin n) :=
  G.neighborFinset x \ SqueezeBench.ExC4.Upper.V003.mset G x

theorem card_lone (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (x : Fin n) :
    G.degree x % 2 ≤ #(lone G x) := by
  have h1 := SqueezeBench.ExC4.Upper.V003.card_mset_le G hG x
  have h2 : #(lone G x) + #(SqueezeBench.ExC4.Upper.V003.mset G x) = G.degree x := by
    rw [lone, Finset.card_sdiff_add_card_eq_card (SqueezeBench.ExC4.Upper.V003.mset_subset G x),
      card_neighborFinset_eq_degree]
  omega

-- The sets `N(y) \ {x}` for `y ∈ N(x)` are pairwise disjoint.
theorem nbr_erase_disjoint (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {x y y' : Fin n}
    (hy : G.Adj x y) (hy' : G.Adj x y') (hne : y ≠ y') :
    Disjoint ((G.neighborFinset y).erase x) ((G.neighborFinset y').erase x) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [Finset.mem_erase, mem_neighborFinset] at hz hz'
  exact hG x z y y' (Ne.symm hz.1) hne hy hz.2.symm hy' hz'.2.symm

-- The local count: the `N(y) \ {x}` and the lone neighbours of `x` are disjoint subsets of
-- the other `n − 1` vertices, and a vertex of odd degree has a lone neighbour.
theorem local_ineq (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) (x : Fin n) :
    sval G x + G.degree x % 2 ≤ n - 1 := by
  set B := (G.neighborFinset x).biUnion (fun y => (G.neighborFinset y).erase x) with hB
  have hcardB : #B = sval G x := by
    rw [hB, Finset.card_biUnion (fun y hy y' hy' hne =>
      nbr_erase_disjoint G hG (by simpa using hy) (by simpa using hy') hne)]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [mem_neighborFinset] at hy
    rw [Finset.card_erase_of_mem (by simpa using hy.symm), card_neighborFinset_eq_degree]
  have hdisj : Disjoint B (lone G x) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hB, Finset.mem_biUnion] at hz
    obtain ⟨y, hy, hzy⟩ := hz
    rw [mem_neighborFinset] at hy
    rw [Finset.mem_erase, mem_neighborFinset] at hzy
    rw [lone, Finset.mem_sdiff, mem_neighborFinset] at hz'
    apply hz'.2
    rw [SqueezeBench.ExC4.Upper.V003.mem_mset]
    exact ⟨y, hz'.1, hy, hzy.2.symm⟩
  have hsub : B ∪ lone G x ⊆ univ.erase x := by
    intro z hz
    rw [Finset.mem_union] at hz
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rcases hz with hz | hz
    · rw [hB, Finset.mem_biUnion] at hz
      obtain ⟨y, -, hzy⟩ := hz
      exact (Finset.mem_erase.mp hzy).1
    · rw [lone, Finset.mem_sdiff, mem_neighborFinset] at hz
      exact (G.ne_of_adj hz.1).symm
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ x),
    Finset.card_univ, Fintype.card_fin, hcardB] at h1
  have h2 := card_lone G hG x
  omega

-- The ordered adjacent pairs.
def apairs : Finset (Fin n × Fin n) := univ.filter (fun p => G.Adj p.1 p.2)

theorem sum_nbr (F : Fin n → Fin n → ℕ) :
    ∑ x, ∑ y ∈ G.neighborFinset x, F x y = ∑ p ∈ apairs G, F p.1 p.2 := by
  rw [apairs, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [neighborFinset_eq_filter, Finset.sum_filter]

theorem sum_swap (F : Fin n → Fin n → ℕ) :
    ∑ p ∈ apairs G, F p.1 p.2 = ∑ p ∈ apairs G, F p.2 p.1 := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp; simp only [apairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.symm
  · intro p hp; simp only [apairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.symm
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

theorem sum_fst (H : Fin n → ℕ) : ∑ p ∈ apairs G, H p.1 = ∑ x, G.degree x * H x := by
  rw [← sum_nbr G (fun x _ => H x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul]

theorem sum_snd (H : Fin n → ℕ) : ∑ p ∈ apairs G, H p.2 = ∑ x, G.degree x * H x := by
  rw [sum_swap G (fun a b => H b)]
  exact sum_fst G H

theorem sum_sval (w : ℕ → ℕ) :
    ∑ p ∈ apairs G, w (G.degree p.1) * (G.degree p.2 - 1) = ∑ x, w (G.degree x) * sval G x := by
  rw [← sum_nbr G (fun x y => w (G.degree x) * (G.degree y - 1))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sval, Finset.mul_sum]

theorem degree_pos_of_adj {x y : Fin n} (h : G.Adj x y) : 1 ≤ G.degree x := by
  rw [← card_neighborFinset_eq_degree]
  exact Finset.card_pos.mpr ⟨y, by simpa using h⟩

/-! ### Putting it together -/

-- With a valid certificate, `2Mm ≤ nβ`: the edge inequality summed over the ordered adjacent
-- pairs, the local count at every vertex, and (D1) at every vertex.
theorem key (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {k : ℕ} {ls : List ℕ} {B : ℕ}
    (h : certOk n k ls B = true) :
    2 * M * #G.edgeFinset ≤ n * betaOf n B := by
  obtain ⟨g, hg⟩ : ∃ g, gOf n B = g := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, betaOf n B = β := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, #G.edgeFinset = m := ⟨_, rfl⟩
  let w : ℕ → ℕ := fun i => wt k ls g i
  let δ : ℕ → ℕ := fun i => dl n k ls g β i
  have hd2 : ∀ p ∈ apairs G,
      w (G.degree p.1) * (G.degree p.1 - 1) + w (G.degree p.2) * (G.degree p.2 - 1)
        ≤ w (G.degree p.1) * (G.degree p.2 - 1) + w (G.degree p.2) * (G.degree p.1 - 1)
          + δ (G.degree p.1) + δ (G.degree p.2) := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    have := d2_all h (degree_pos_of_adj G hadj) (degree_pos_of_adj G hadj.symm)
    rw [hg, hβ] at this
    exact this
  have hd1 : ∀ x : Fin n,
      M * G.degree x + w (G.degree x) * (n - 1 - G.degree x % 2) + G.degree x * δ (G.degree x)
        ≤ β + G.degree x * (w (G.degree x) * (G.degree x - 1)) := by
    intro x
    have := d1_all h (G.degree x)
    rw [hg, hβ] at this
    exact this
  -- the three vertex sums
  obtain ⟨S1, hS1⟩ : ∃ S, ∑ x, G.degree x * (w (G.degree x) * (G.degree x - 1)) = S := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S, ∑ x, w (G.degree x) * sval G x = S := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S, ∑ x, G.degree x * δ (G.degree x) = S := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ S, ∑ x, w (G.degree x) * (n - 1 - G.degree x % 2) = S := ⟨_, rfl⟩
  have hedge := Finset.sum_le_sum hd2
  have e1 : ∑ p ∈ apairs G,
      (w (G.degree p.1) * (G.degree p.1 - 1) + w (G.degree p.2) * (G.degree p.2 - 1))
        = S1 + S1 := by
    rw [Finset.sum_add_distrib, sum_fst G (fun x => w (G.degree x) * (G.degree x - 1)),
      sum_snd G (fun x => w (G.degree x) * (G.degree x - 1)), hS1]
  have e2 : ∑ p ∈ apairs G,
      (w (G.degree p.1) * (G.degree p.2 - 1) + w (G.degree p.2) * (G.degree p.1 - 1)
        + δ (G.degree p.1) + δ (G.degree p.2)) = S2 + S2 + S3 + S3 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_fst G (fun x => δ (G.degree x)), sum_snd G (fun x => δ (G.degree x)), hS3,
      ← sum_swap G (fun a b => w (G.degree a) * (G.degree b - 1)), sum_sval G w, hS2]
  rw [e1, e2] at hedge
  have hloc : S2 ≤ W := by
    rw [← hS2, ← hW]
    refine Finset.sum_le_sum fun x _ => Nat.mul_le_mul_left _ ?_
    have := local_ineq G hG x
    omega
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset (Fin n))) => hd1 x
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hS1, hS3, hW,
    G.sum_degrees_eq_twice_card_edges, hm] at hsum
  rw [hβ, hm]
  have e3 : 2 * M * m = M * (2 * m) := by ring
  omega

theorem edges_le (hG : SqueezeBench.ExC4.NoTwoCommonNeighbours G) {k : ℕ} {ls : List ℕ} {B : ℕ}
    (h : certOk n k ls B = true) : #G.edgeFinset ≤ B := by
  have h1 := key G hG h
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 * M * (B + 1) = Q := ⟨_, rfl⟩
  have h2 : n * betaOf n B ≤ Q - 1 := by
    rw [betaOf, Nat.mul_comm, hQ]
    exact Nat.div_mul_le_self _ _
  have hM : 0 < M := by decide
  have hQpos : 0 < Q := by rw [← hQ]; positivity
  have h3 : 2 * M * #G.edgeFinset < 2 * M * (B + 1) := by rw [hQ]; omega
  have h4 := Nat.lt_of_mul_lt_mul_left h3
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
      have hV4 : SqueezeBench.ExC4.f (k + 1) ≤ SqueezeBench.ExC4.Upper.V004.record (k + 1) :=
        SqueezeBench.ExC4.Upper.V004.valid (k + 1)
      rcases hl : lookup (k + 1) with _ | ⟨k', ls, B⟩
      · simp only [v, hl]
        exact hV4
      · simp only [v, hl]
        split
        · rename_i hok
          refine SqueezeBench.ExC4.f_le_of_forall_noTwoCommonNeighbours (by simp) ?_
          intro G _ hG
          exact edges_le G hG hok
        · exact hV4

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExC4.Upper.V004.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V004.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V004.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 15) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Upper.V005
