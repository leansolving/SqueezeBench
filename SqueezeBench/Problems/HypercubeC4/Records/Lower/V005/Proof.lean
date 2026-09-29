import SqueezeBench.Problems.HypercubeC4.Records.Lower.V005.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V004.Proof

/-! Record V005 for HypercubeC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V005.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V005

open Finset SimpleGraph

-- Flipping two different bits commutes.
theorem flip_comm {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (h : i ≠ j) :
    HypercubeC4.flip (HypercubeC4.flip x i) j = HypercubeC4.flip (HypercubeC4.flip x j) i := by
  funext k
  rcases eq_or_ne k i with rfl | hki
  · simp [HypercubeC4.flip_apply, h]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [HypercubeC4.flip_apply, hki]
    · simp [HypercubeC4.flip_apply, hki, hkj]

-- V001's parity rule does not depend on which end of the edge it is read at.
theorem keep_symm {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    V001.keep (HypercubeC4.flip x i) i ↔ V001.keep x i := by
  unfold V001.keep
  rw [HypercubeC4.flip_flip]
  constructor <;> intro h <;> omega

-- The keep-predicate of the construction: in the three special directions `a`, `b`, `c` the
-- optimal 9-edge `C₄`-free subgraph of `Q₃`, elsewhere V001's parity half.
def kb {n : ℕ} (a b c : Fin n) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = a then !(!x b && !x c)
  else if i = b then !(x a && x c)
  else if i = c then !(!x a && x b)
  else decide (V001.keep x i)

theorem kb_a {n : ℕ} (a b c : Fin n) (x : Fin n → Bool) :
    kb a b c x a = !(!x b && !x c) := by simp [kb]

theorem kb_b {n : ℕ} {a b : Fin n} (c : Fin n) (hab : a ≠ b) (x : Fin n → Bool) :
    kb a b c x b = !(x a && x c) := by simp [kb, Ne.symm hab]

theorem kb_c {n : ℕ} {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c) (x : Fin n → Bool) :
    kb a b c x c = !(!x a && x b) := by simp [kb, Ne.symm hac, Ne.symm hbc]

theorem kb_other {n : ℕ} (a b c : Fin n) (x : Fin n → Bool) {i : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) (hic : i ≠ c) :
    kb a b c x i = decide (V001.keep x i) := by simp [kb, hia, hib, hic]

-- An edge is kept from both of its ends.
theorem kb_flip_self {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin n → Bool) (i : Fin n) : kb a b c (HypercubeC4.flip x i) i = kb a b c x i := by
  rcases eq_or_ne i a with rfl | hia
  · rw [kb_a, kb_a]
    simp [HypercubeC4.flip_apply, Ne.symm hab, Ne.symm hac]
  · rcases eq_or_ne i b with rfl | hib
    · rw [kb_b _ (Ne.symm hia), kb_b _ (Ne.symm hia)]
      simp [HypercubeC4.flip_apply, hab, Ne.symm hbc]
    · rcases eq_or_ne i c with rfl | hic
      · rw [kb_c (Ne.symm hia) (Ne.symm hib), kb_c (Ne.symm hia) (Ne.symm hib)]
        simp [HypercubeC4.flip_apply, hac, hbc]
      · rw [kb_other a b c _ hia hib hic, kb_other a b c _ hia hib hic]
        simp [keep_symm]

-- The subgraph of the cube that keeps exactly the edges named by `kb`.
def Q {n : ℕ} (a b c : Fin n) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1 ∧
    ∀ i, y = HypercubeC4.flip x i → (kb a b c x i = true ∧ kb a b c y i = true)
  symm := ⟨fun x y h => ⟨by rw [hammingDist_comm]; exact h.1, fun i hi => by
    have hy : y = HypercubeC4.flip x i := by rw [hi, HypercubeC4.flip_flip]
    exact ⟨(h.2 i hy).2, (h.2 i hy).1⟩⟩⟩
  loopless := ⟨fun x h => absurd h.1 (by simp)⟩

instance decQ {n : ℕ} (a b c : Fin n) : DecidableRel (Q a b c).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1 ∧
    ∀ i, y = HypercubeC4.flip x i → (kb a b c x i = true ∧ kb a b c y i = true)))

theorem Q_le {n : ℕ} (a b c : Fin n) : Q a b c ≤ HypercubeC4.hypercube n := fun _ _ h => h.1

theorem adj_flip {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin n → Bool) (i : Fin n) :
    (Q a b c).Adj x (HypercubeC4.flip x i) ↔ kb a b c x i = true := by
  constructor
  · intro h
    exact (h.2 i rfl).1
  · intro hk
    refine ⟨HypercubeC4.hypercube_adj.mp (HypercubeC4.hypercube_adj_iff.mpr ⟨i, rfl⟩), ?_⟩
    intro j hj
    have hij : i = j := V001.flip_inj x hj
    subst hij
    exact ⟨hk, by rw [kb_flip_self hab hac hbc]; exact hk⟩

-- The three special directions carry the optimal 9-edge `C₄`-free subgraph of `Q₃`: each of its
-- three squares loses an edge. One lemma per pair of special directions.
theorem no_square_ab {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin n → Bool) (h1 : kb a b c x a = true) (h2 : kb a b c x b = true)
    (h3 : kb a b c (HypercubeC4.flip x a) b = true)
    (h4 : kb a b c (HypercubeC4.flip x b) a = true) : False := by
  have fa_a : HypercubeC4.flip x a a = !x a := by simp [HypercubeC4.flip_apply]
  have fa_c : HypercubeC4.flip x a c = x c := by simp [HypercubeC4.flip_apply, Ne.symm hac]
  have fb_b : HypercubeC4.flip x b b = !x b := by simp [HypercubeC4.flip_apply]
  have fb_c : HypercubeC4.flip x b c = x c := by simp [HypercubeC4.flip_apply, Ne.symm hbc]
  rw [kb_a] at h1
  rw [kb_b _ hab] at h2
  rw [kb_b _ hab, fa_a, fa_c] at h3
  rw [kb_a, fb_b, fb_c] at h4
  revert h1 h2 h3 h4
  cases x a <;> cases x b <;> cases x c <;> simp

theorem no_square_ac {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin n → Bool) (h1 : kb a b c x a = true) (h2 : kb a b c x c = true)
    (h3 : kb a b c (HypercubeC4.flip x a) c = true)
    (h4 : kb a b c (HypercubeC4.flip x c) a = true) : False := by
  have fa_a : HypercubeC4.flip x a a = !x a := by simp [HypercubeC4.flip_apply]
  have fa_b : HypercubeC4.flip x a b = x b := by simp [HypercubeC4.flip_apply, Ne.symm hab]
  have fc_b : HypercubeC4.flip x c b = x b := by simp [HypercubeC4.flip_apply, hbc]
  have fc_c : HypercubeC4.flip x c c = !x c := by simp [HypercubeC4.flip_apply]
  rw [kb_a] at h1
  rw [kb_c hac hbc] at h2
  rw [kb_c hac hbc, fa_a, fa_b] at h3
  rw [kb_a, fc_b, fc_c] at h4
  revert h1 h2 h3 h4
  cases x a <;> cases x b <;> cases x c <;> simp

theorem no_square_bc {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin n → Bool) (h1 : kb a b c x b = true) (h2 : kb a b c x c = true)
    (h3 : kb a b c (HypercubeC4.flip x b) c = true)
    (h4 : kb a b c (HypercubeC4.flip x c) b = true) : False := by
  have fb_a : HypercubeC4.flip x b a = x a := by simp [HypercubeC4.flip_apply, hab]
  have fb_b : HypercubeC4.flip x b b = !x b := by simp [HypercubeC4.flip_apply]
  have fc_a : HypercubeC4.flip x c a = x a := by simp [HypercubeC4.flip_apply, hac]
  have fc_c : HypercubeC4.flip x c c = !x c := by simp [HypercubeC4.flip_apply]
  rw [kb_b _ hab] at h1
  rw [kb_c hac hbc] at h2
  rw [kb_c hac hbc, fb_a, fb_b] at h3
  rw [kb_b _ hab, fc_a, fc_c] at h4
  revert h1 h2 h3 h4
  cases x a <;> cases x b <;> cases x c <;> simp

-- No square survives: a square with a generic direction loses one of its two parallel edges to
-- V001's parity rule, and a square inside the three special directions is a square of `Q₃`.
theorem not_hasSquare {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ HypercubeC4.HasSquare (Q a b c) := by
  rintro ⟨x, i, j, hij, h1, h2, h3, h4⟩
  rw [adj_flip hab hac hbc] at h1 h2 h3
  rw [flip_comm x hij, adj_flip hab hac hbc] at h4
  by_cases hi : i = a ∨ i = b ∨ i = c
  · by_cases hj : j = a ∨ j = b ∨ j = c
    · rcases hi with h | h | h <;> rcases hj with h' | h' | h' <;>
        rw [h] at h1 h3 h4 <;> rw [h'] at h2 h3 h4 <;>
        first
          | exact hij (h.trans h'.symm)
          | exact no_square_ab hab hac hbc x h1 h2 h3 h4
          | exact no_square_ab hab hac hbc x h2 h1 h4 h3
          | exact no_square_ac hab hac hbc x h1 h2 h3 h4
          | exact no_square_ac hab hac hbc x h2 h1 h4 h3
          | exact no_square_bc hab hac hbc x h1 h2 h3 h4
          | exact no_square_bc hab hac hbc x h2 h1 h4 h3
    · push_neg at hj
      rw [kb_other a b c x hj.1 hj.2.1 hj.2.2, decide_eq_true_eq] at h2
      rw [kb_other a b c _ hj.1 hj.2.1 hj.2.2, decide_eq_true_eq] at h3
      exact (V001.keep_flip x hij).mp h3 h2
  · push_neg at hi
    rw [kb_other a b c x hi.1 hi.2.1 hi.2.2, decide_eq_true_eq] at h1
    rw [kb_other a b c _ hi.1 hi.2.1 hi.2.2, decide_eq_true_eq] at h4
    exact (V001.keep_flip x (Ne.symm hij)).mp h4 h1

theorem degree_eq {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin n → Bool) :
    (Q a b c).degree x = #(univ.filter (fun i : Fin n => kb a b c x i = true)) := by
  show ((Q a b c).neighborFinset x).card = _
  refine (Finset.card_bij (fun i _ => HypercubeC4.flip x i) ?_ ?_ ?_).symm
  · intro d hd
    simp only [Finset.mem_filter] at hd
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ((adj_flip hab hac hbc x d).mpr hd.2)
  · intro d _ e _ hde
    exact V001.flip_inj x hde
  · intro y hy
    have hadj : (Q a b c).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    obtain ⟨d, rfl⟩ := HypercubeC4.hypercube_adj_iff.mp (Q_le a b c hadj)
    exact ⟨d, by simp [Finset.mem_filter, (adj_flip hab hac hbc x d).mp hadj], rfl⟩

-- Halving: if `p` is invariant under flipping bit `j`, fixing bit `j` halves the count.
theorem card_split {n : ℕ} (p : (Fin n → Bool) → Prop) [DecidablePred p] (j : Fin n) (α : Bool)
    (hp : ∀ x, p (HypercubeC4.flip x j) ↔ p x) :
    2 * #(univ.filter (fun x : Fin n → Bool => x j = α ∧ p x)) = #(univ.filter p) := by
  have hbij : #(univ.filter (fun x : Fin n → Bool => x j = α ∧ p x))
      = #(univ.filter (fun x : Fin n → Bool => ¬ x j = α ∧ p x)) := by
    refine Finset.card_bij' (fun x _ => HypercubeC4.flip x j) (fun y _ => HypercubeC4.flip y j)
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨?_, (hp y).mpr hy.2⟩
      have hj : HypercubeC4.flip y j j = !y j := by simp [HypercubeC4.flip_apply]
      rw [hj, hy.1]
      simp
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨?_, (hp y).mpr hy.2⟩
      have hj : HypercubeC4.flip y j j = !y j := by simp [HypercubeC4.flip_apply]
      rw [hj]
      cases hyj : y j <;> cases α <;> simp_all
    · intro y _; exact HypercubeC4.flip_flip y j
    · intro y _; exact HypercubeC4.flip_flip y j
  have hsp : #(univ.filter (fun x : Fin n → Bool => x j = α ∧ p x))
      + #(univ.filter (fun x : Fin n → Bool => ¬ x j = α ∧ p x)) = #(univ.filter p) := by
    have e1 : univ.filter (fun x : Fin n → Bool => x j = α ∧ p x)
        = (univ.filter p).filter (fun x : Fin n → Bool => x j = α) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    have e2 : univ.filter (fun x : Fin n → Bool => ¬ x j = α ∧ p x)
        = (univ.filter p).filter (fun x : Fin n → Bool => ¬ x j = α) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [e1, e2, Finset.card_filter_add_card_filter_not]
  omega

theorem card_one {n : ℕ} (j : Fin n) (α : Bool) :
    2 * #(univ.filter (fun x : Fin n → Bool => x j = α)) = 2 ^ n := by
  have h := card_split (n := n) (fun _ => True) j α (fun _ => Iff.rfl)
  simpa using h

theorem card_two {n : ℕ} {p q : Fin n} (hpq : p ≠ q) (β γ : Bool) :
    4 * #(univ.filter (fun x : Fin n → Bool => x p = β ∧ x q = γ)) = 2 ^ n := by
  have h1 := card_split (n := n) (fun x => x q = γ) p β
    (fun x => by simp [HypercubeC4.flip_apply, Ne.symm hpq])
  have h2 := card_one q γ
  omega

theorem card_not_two {n : ℕ} {p q : Fin n} (hpq : p ≠ q) (β γ : Bool)
    (S : (Fin n → Bool) → Bool) (hS : ∀ x, S x = true ↔ ¬(x p = β ∧ x q = γ)) :
    4 * #(univ.filter (fun x : Fin n → Bool => S x = true)) = 3 * 2 ^ n := by
  have he : univ.filter (fun x : Fin n → Bool => S x = true)
      = univ.filter (fun x : Fin n → Bool => ¬(x p = β ∧ x q = γ)) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS y]
  rw [he]
  have hsp : #(univ.filter (fun x : Fin n → Bool => x p = β ∧ x q = γ))
      + #(univ.filter (fun x : Fin n → Bool => ¬(x p = β ∧ x q = γ))) = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have h4 := card_two hpq β γ
  omega

theorem card_special {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {i : Fin n} (hi : i = a ∨ i = b ∨ i = c) :
    4 * #(univ.filter (fun x : Fin n → Bool => kb a b c x i = true)) = 3 * 2 ^ n := by
  rcases hi with rfl | rfl | rfl
  · exact card_not_two hbc false false _ (fun x => by rw [kb_a]; cases x b <;> cases x c <;> simp)
  · exact card_not_two hac true true _
      (fun x => by rw [kb_b _ hab]; cases x a <;> cases x c <;> simp)
  · exact card_not_two hab false true _
      (fun x => by rw [kb_c hac hbc]; cases x a <;> cases x b <;> simp)

theorem card_generic {n : ℕ} (hn : 3 ≤ n) {a b c : Fin n} {i : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) (hic : i ≠ c) :
    4 * #(univ.filter (fun x : Fin n → Bool => kb a b c x i = true)) = 2 * 2 ^ n := by
  have he : univ.filter (fun x : Fin n → Bool => kb a b c x i = true)
      = univ.filter (fun x : Fin n → Bool => V001.keep x i) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, kb_other a b c y hia hib hic,
      decide_eq_true_eq]
  rw [he, V001.card_keep (by omega) i]
  have h : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]; ring
  omega

theorem sum_degree {n : ℕ} (hn : 3 ≤ n) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    4 * ∑ x : Fin n → Bool, (Q a b c).degree x = (2 * n + 3) * 2 ^ n := by
  have h1 : ∀ x : Fin n → Bool,
      (Q a b c).degree x = ∑ i : Fin n, if kb a b c x i = true then 1 else 0 := by
    intro x
    rw [degree_eq hab hac hbc, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm, Finset.mul_sum]
  have h2 : ∀ i : Fin n, 4 * (∑ x : Fin n → Bool, if kb a b c x i = true then 1 else 0)
      = if i = a ∨ i = b ∨ i = c then 3 * 2 ^ n else 2 * 2 ^ n := by
    intro i
    rw [← Finset.card_filter]
    by_cases hi : i = a ∨ i = b ∨ i = c
    · rw [if_pos hi]; exact card_special hab hac hbc hi
    · rw [if_neg hi]
      push_neg at hi
      exact card_generic hn hi.1 hi.2.1 hi.2.2
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  have hmem : ∀ i : Fin n, (i ∈ ({a, b, c} : Finset (Fin n))) ↔ (i = a ∨ i = b ∨ i = c) := by
    intro i; simp
  have hcardS : (({a, b, c} : Finset (Fin n))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hsd := Finset.sum_sdiff (f := fun i : Fin n =>
      if i = a ∨ i = b ∨ i = c then 3 * 2 ^ n else 2 * 2 ^ n)
    (Finset.subset_univ ({a, b, c} : Finset (Fin n)))
  have e1 : ∑ i ∈ ({a, b, c} : Finset (Fin n)),
      (if i = a ∨ i = b ∨ i = c then 3 * 2 ^ n else 2 * 2 ^ n) = 3 * (3 * 2 ^ n) := by
    rw [Finset.sum_congr rfl (fun i hi => if_pos ((hmem i).mp hi)), Finset.sum_const, hcardS,
      smul_eq_mul]
  have e2 : ∑ i ∈ (univ \ ({a, b, c} : Finset (Fin n))),
      (if i = a ∨ i = b ∨ i = c then 3 * 2 ^ n else 2 * 2 ^ n) = (n - 3) * (2 * 2 ^ n) := by
    rw [Finset.sum_congr rfl (fun i hi => if_neg (fun hc =>
      (Finset.mem_sdiff.mp hi).2 ((hmem i).mpr hc))), Finset.sum_const,
      Finset.card_sdiff, Finset.inter_univ, hcardS, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  rw [← hsd, e1, e2]
  obtain ⟨m, hm⟩ : ∃ m, n - 3 = m := ⟨n - 3, rfl⟩
  have hnm : n = m + 3 := by omega
  subst hnm
  rw [hm]
  ring

theorem card_edges {n : ℕ} (hn : 3 ≤ n) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : #((Q a b c).edgeFinset) = (2 * n + 3) * 2 ^ (n - 3) := by
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (Q a b c)
  have hs := sum_degree hn hab hac hbc
  rw [h] at hs
  have h8 : (2 : ℕ) ^ n = 8 * 2 ^ (n - 3) := by
    conv_lhs => rw [show n = (n - 3) + 3 from by omega]
    rw [pow_add]; ring
  rw [h8] at hs
  have : 8 * #((Q a b c).edgeFinset) = 8 * ((2 * n + 3) * 2 ^ (n - 3)) := by linarith
  omega

theorem prod3_le {n : ℕ} (hn : 3 ≤ n) : prod3 n ≤ SqueezeBench.HypercubeC4.f n := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have h2 : (2 : ℕ) < n := by omega
  set a : Fin n := ⟨0, h0⟩ with ha
  set b : Fin n := ⟨1, h1⟩ with hb
  set c : Fin n := ⟨2, h2⟩ with hc
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc, Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc, Fin.ext_iff]
  have hr : prod3 n = (2 * n + 3) * 2 ^ (n - 3) := by
    simp [prod3, Nat.not_lt.mpr hn]
  rw [hr, ← card_edges hn hab hac hbc]
  exact HypercubeC4.le_f_of_not_hasSquare (by rw [HypercubeC4.nMin_eq]; omega) (Q_le a b c)
    (not_hasSquare hab hac hbc)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.maxWith_valid V004.valid (fun n => by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · simp [prod3, hn]
    · exact prod3_le hn)

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V004.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V004.record record :=
  SqueezeBench.maxWith_strict (n₀ := 6) (by decide) (by decide)

end SqueezeBench.HypercubeC4.Lower.V005
