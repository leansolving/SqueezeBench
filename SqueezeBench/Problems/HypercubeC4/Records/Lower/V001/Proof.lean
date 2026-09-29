import SqueezeBench.Problems.HypercubeC4.Records.Lower.V001.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V000.Proof

/-! Record V001 for HypercubeC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V001.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V001

open Finset SimpleGraph

-- The number of ones of a binary word.
def wt {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i : Fin n => x i = true)).card

-- Flipping a one lowers the weight by one.
theorem wt_flip_true {n : ℕ} {x : Fin n → Bool} {i : Fin n} (h : x i = true) :
    wt x = wt (HypercubeC4.flip x i) + 1 := by
  have hset : Finset.univ.filter (fun j : Fin n => HypercubeC4.flip x i j = true)
      = (Finset.univ.filter (fun j : Fin n => x j = true)).erase i := by
    ext j
    by_cases hj : j = i <;> simp [HypercubeC4.flip_apply, hj, h]
  have hmem : i ∈ Finset.univ.filter (fun j : Fin n => x j = true) := by simp [h]
  unfold wt
  rw [hset, Finset.card_erase_of_mem hmem]
  have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
  omega

-- Flipping a zero raises the weight by one.
theorem wt_flip_false {n : ℕ} {x : Fin n → Bool} {i : Fin n} (h : x i = false) :
    wt (HypercubeC4.flip x i) = wt x + 1 := by
  have hset : Finset.univ.filter (fun j : Fin n => HypercubeC4.flip x i j = true)
      = insert i (Finset.univ.filter (fun j : Fin n => x j = true)) := by
    ext j
    by_cases hj : j = i <;> simp [HypercubeC4.flip_apply, hj, h]
  have hmem : i ∉ Finset.univ.filter (fun j : Fin n => x j = true) := by simp [h]
  unfold wt
  rw [hset, Finset.card_insert_of_notMem hmem]

-- The parity subgraph: keep the edge `{x, y}` of the cube when `wt x + wt y ≡ 1 mod 4`, that is
-- when the bits the two words share have an even sum.
def P (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1 ∧ (wt x + wt y) % 4 = 1
  symm := ⟨fun x y h => ⟨by rw [hammingDist_comm]; exact h.1, by omega⟩⟩
  loopless := ⟨fun x h => absurd h.1 (by simp)⟩

instance decP (n : ℕ) : DecidableRel (P n).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1 ∧ (wt x + wt y) % 4 = 1))

theorem P_le (n : ℕ) : P n ≤ HypercubeC4.hypercube n := fun _ _ h => h.1

-- The edges of `P n` at `x`, named by the direction they run in.
def keep {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Prop :=
  (wt x + wt (HypercubeC4.flip x i)) % 4 = 1

instance decKeep {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Decidable (keep x i) :=
  inferInstanceAs (Decidable ((wt x + wt (HypercubeC4.flip x i)) % 4 = 1))

theorem adj_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (P n).Adj x (HypercubeC4.flip x i) ↔ keep x i := by
  constructor
  · intro h; exact h.2
  · intro h
    exact ⟨HypercubeC4.hypercube_adj.mp (HypercubeC4.hypercube_adj_iff.mpr ⟨i, rfl⟩), h⟩

-- Flipping another bit toggles whether the edge in direction `i` is kept.
theorem keep_flip {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (hj : j ≠ i) :
    keep (HypercubeC4.flip x j) i ↔ ¬ keep x i := by
  have hb : HypercubeC4.flip x j i = x i := by
    simp [HypercubeC4.flip_apply, Ne.symm hj]
  unfold keep
  cases hxi : x i <;> cases hxj : x j
  · have a := wt_flip_false hxi
    have b := wt_flip_false hxj
    have c := wt_flip_false (x := HypercubeC4.flip x j) (i := i) (by rw [hb]; exact hxi)
    omega
  · have a := wt_flip_false hxi
    have b := wt_flip_true hxj
    have c := wt_flip_false (x := HypercubeC4.flip x j) (i := i) (by rw [hb]; exact hxi)
    omega
  · have a := wt_flip_true hxi
    have b := wt_flip_false hxj
    have c := wt_flip_true (x := HypercubeC4.flip x j) (i := i) (by rw [hb]; exact hxi)
    omega
  · have a := wt_flip_true hxi
    have b := wt_flip_true hxj
    have c := wt_flip_true (x := HypercubeC4.flip x j) (i := i) (by rw [hb]; exact hxi)
    omega

-- No square survives: in each of the two directions exactly one of the two parallel edges is kept.
theorem not_hasSquare (n : ℕ) : ¬ HypercubeC4.HasSquare (P n) := by
  rintro ⟨x, i, j, hij, h1, h2, h3, h4⟩
  have hji : HypercubeC4.flip x i j = x j := by
    simp [HypercubeC4.flip_apply, Ne.symm hij]
  have e1 : (wt x + wt (HypercubeC4.flip x i)) % 4 = 1 := h1.2
  have e2 : (wt x + wt (HypercubeC4.flip x j)) % 4 = 1 := h2.2
  have e3 : (wt (HypercubeC4.flip x i)
      + wt (HypercubeC4.flip (HypercubeC4.flip x i) j)) % 4 = 1 := h3.2
  have e4 : (wt (HypercubeC4.flip x j)
      + wt (HypercubeC4.flip (HypercubeC4.flip x i) j)) % 4 = 1 := h4.2
  cases hxi : x i <;> cases hxj : x j
  · have a := wt_flip_false hxi
    have b := wt_flip_false hxj
    have c := wt_flip_false (x := HypercubeC4.flip x i) (i := j) (by rw [hji]; exact hxj)
    omega
  · have a := wt_flip_false hxi
    have b := wt_flip_true hxj
    have c := wt_flip_true (x := HypercubeC4.flip x i) (i := j) (by rw [hji]; exact hxj)
    omega
  · have a := wt_flip_true hxi
    have b := wt_flip_false hxj
    have c := wt_flip_false (x := HypercubeC4.flip x i) (i := j) (by rw [hji]; exact hxj)
    omega
  · have a := wt_flip_true hxi
    have b := wt_flip_true hxj
    have c := wt_flip_true (x := HypercubeC4.flip x i) (i := j) (by rw [hji]; exact hxj)
    omega

theorem flip_inj {n : ℕ} (x : Fin n → Bool) {i j : Fin n}
    (h : HypercubeC4.flip x i = HypercubeC4.flip x j) : i = j := by
  by_contra hne
  have hi := congrFun h i
  rw [HypercubeC4.flip_apply, HypercubeC4.flip_apply] at hi
  simp [hne] at hi

-- The degree of `x` counts the directions whose edge at `x` is kept.
theorem degree_eq {n : ℕ} (x : Fin n → Bool) :
    (P n).degree x = (Finset.univ.filter (fun i : Fin n => keep x i)).card := by
  show ((P n).neighborFinset x).card = _
  refine (Finset.card_bij (fun i _ => HypercubeC4.flip x i) ?_ ?_ ?_).symm
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ((adj_flip x a).mpr ha.2)
  · intro a _ b _ hab
    exact flip_inj x hab
  · intro y hy
    have hadj : (P n).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    obtain ⟨i, rfl⟩ := HypercubeC4.hypercube_adj_iff.mp (P_le n hadj)
    exact ⟨i, by simp [Finset.mem_filter, (adj_flip x i).mp hadj], rfl⟩

-- For each direction, exactly half of the words keep their edge in that direction.
theorem card_keep {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (Finset.univ.filter (fun x : Fin n → Bool => keep x i)).card = 2 ^ (n - 1) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  have hbij : (Finset.univ.filter (fun x : Fin n → Bool => keep x i)).card
      = (Finset.univ.filter (fun x : Fin n → Bool => ¬ keep x i)).card := by
    refine Finset.card_bij' (fun x _ => HypercubeC4.flip x j) (fun y _ => HypercubeC4.flip y j)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact fun hcon => (keep_flip a hj).mp hcon ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (keep_flip a hj).mpr ha
    · intro a _; exact HypercubeC4.flip_flip a j
    · intro a _; exact HypercubeC4.flip_flip a j
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Bool))) (p := fun x => keep x i)
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Finset.card_univ]
  have h2 : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  rw [hcard, h2] at htot
  omega

theorem sum_degree {n : ℕ} (hn : 2 ≤ n) :
    ∑ x : Fin n → Bool, (P n).degree x = n * 2 ^ (n - 1) := by
  have h1 : ∀ x : Fin n → Bool, (P n).degree x = ∑ i : Fin n, if keep x i then 1 else 0 := by
    intro x
    rw [degree_eq, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm]
  have h2 : ∀ i : Fin n, (∑ x : Fin n → Bool, if keep x i then 1 else 0) = 2 ^ (n - 1) := by
    intro i
    rw [← Finset.card_filter]
    exact card_keep hn i
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

theorem card_edges {n : ℕ} (hn : 2 ≤ n) : ((P n).edgeFinset).card = n * 2 ^ (n - 2) := by
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (P n)
  rw [sum_degree hn] at h
  have h2 : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have hns : n - 1 = (n - 2) + 1 := by omega
    rw [hns, pow_succ]
    ring
  rw [h2] at h
  have h3 : 2 * (n * 2 ^ (n - 2)) = 2 * ((P n).edgeFinset).card := by
    rw [← h]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h3).symm

theorem one_le_f_one : 1 ≤ SqueezeBench.HypercubeC4.f 1 := by
  have hsq : ¬ HypercubeC4.HasSquare (HypercubeC4.hypercube 1) := by
    rintro ⟨y, a, b, hab, -⟩
    exact hab (Subsingleton.elim a b)
  have hle := HypercubeC4.le_f_of_not_hasSquare (G := HypercubeC4.hypercube 1)
    (by rw [HypercubeC4.nMin_eq]) le_rfl hsq
  have hc : ((HypercubeC4.hypercube 1).edgeFinset).card = 1 := by decide
  omega

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Nat.zero_le _
    · have hr : record 1 = 1 := by norm_num [record]
      rw [hr]
      exact one_le_f_one
  · show n * 2 ^ (n - 2) ≤ SqueezeBench.HypercubeC4.f n
    rw [← card_edges hn]
    exact HypercubeC4.le_f_of_not_hasSquare (by rw [HypercubeC4.nMin_eq]; omega)
      (P_le n) (not_hasSquare n)

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V000.record record :=
  fun _ => Nat.zero_le _

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V000.record record :=
  ⟨6, by decide, by decide⟩

end SqueezeBench.HypercubeC4.Lower.V001
