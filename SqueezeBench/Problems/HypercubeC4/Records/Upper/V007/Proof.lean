import SqueezeBench.Problems.HypercubeC4.Records.Upper.V007.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V006.Proof

/-! Record V007 for HypercubeC4, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V007.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V007

open Finset SimpleGraph

/-! ## Flip algebra -/

theorem flip_flip_flip_comm {n : ℕ} (x : Fin n → Bool) (a b c : Fin n) :
    flip (flip (flip x a) b) c = flip (flip (flip x a) c) b :=
  V005.flip_comm (flip x a) b c

-- `flip (opp x i j) i = flip x j`, with no side condition.
theorem flip_opp_l {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    flip (V002.opp x i j) i = flip x j := by
  simp only [V002.opp]
  rw [V005.flip_comm (flip x i) j i, flip_flip]

theorem flip_opp_r {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    flip (V002.opp x i j) j = flip x i := by
  simp only [V002.opp, flip_flip]

-- The antipode `flip (opp x i j) k` of the block, flipped once more.
theorem flip_anti_i {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) :
    flip (flip (V002.opp x i j) k) i = V002.opp x j k := by
  simp only [V002.opp]
  rw [V005.flip_comm (flip (flip x i) j) k i, V005.flip_comm (flip x i) j i, flip_flip]

theorem flip_anti_j {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) :
    flip (flip (V002.opp x i j) k) j = V002.opp x i k := by
  simp only [V002.opp]
  rw [V005.flip_comm (flip (flip x i) j) k j, flip_flip]

theorem flip_anti_k {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) :
    flip (flip (V002.opp x i j) k) k = V002.opp x i j := flip_flip _ _

/-! ## Membership in the direction sets -/

theorem mem_A_flip {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i : Fin n)
    (x : Fin n → Bool) : flip x i ∈ V002.A G i ↔ x ∈ V002.A G i :=
  ⟨fun h => by simpa using V005.flip_mem_A G h, fun h => V005.flip_mem_A G h⟩

-- The four edges of a square cannot all be present.
theorem not_square {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) {x : Fin n → Bool}
    (h1 : x ∈ V002.A G i) (h2 : x ∈ V002.A G j) (h3 : flip x i ∈ V002.A G j)
    (h4 : flip x j ∈ V002.A G i) : False := by
  rw [V005.mem_A] at h1 h2 h3 h4
  refine hG ⟨x, i, j, hij, h1, h2, h3, ?_⟩
  rwa [V005.flip_comm x i j]

-- Opposite corners of a square cannot both carry both of its edges.
theorem not_opp {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j : Fin n} (hij : i ≠ j) {x : Fin n → Bool}
    (h1 : x ∈ V002.A G i) (h2 : x ∈ V002.A G j) (h3 : V002.opp x i j ∈ V002.A G i)
    (h4 : V002.opp x i j ∈ V002.A G j) : False := by
  rw [← mem_A_flip, flip_opp_l] at h3
  rw [← mem_A_flip, flip_opp_r] at h4
  exact not_square G hG hij h1 h2 h4 h3

/-! ## The block weight -/

-- All three edges of the block present at `x`.
abbrev full {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i j k : Fin n)
    (x : Fin n → Bool) : Prop :=
  x ∈ V002.A G i ∧ x ∈ V002.A G j ∧ x ∈ V002.A G k

-- No edge of the block at `x`.
abbrev iso {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i j k : Fin n)
    (x : Fin n → Bool) : Prop :=
  x ∉ V002.A G i ∧ x ∉ V002.A G j ∧ x ∉ V002.A G k

-- The two far edges of the square at `x` in directions `i, j` are present.
def blue {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (x : Fin n → Bool)
    (i j : Fin n) : Prop :=
  flip x i ∈ V002.A G j ∧ flip x j ∈ V002.A G i

instance {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (x : Fin n → Bool)
    (i j : Fin n) : Decidable (blue G x i j) := by unfold blue; infer_instance

def β {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (x : Fin n → Bool)
    (i j : Fin n) : ℕ :=
  if blue G x i j then 1 else 0

-- The number of blue pairs among the three directions.
def bc {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i j k : Fin n)
    (x : Fin n → Bool) : ℕ :=
  β G x i j + β G x i k + β G x j k

-- Chung's block weight: `4` for a full corner, `(b − 1)²` for an isolated one.
def g {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (i j k : Fin n)
    (x : Fin n → Bool) : ℤ :=
  (if full G i j k x then 4 else 0) + (if iso G i j k x then ((bc G i j k x : ℤ) - 1) ^ 2 else 0)

theorem blue_comm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (i j : Fin n) : blue G x i j ↔ blue G x j i := And.comm

theorem β_comm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (i j : Fin n) : β G x i j = β G x j i := by
  unfold β
  by_cases h : blue G x i j
  · rw [if_pos h, if_pos ((blue_comm G x i j).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((blue_comm G x i j).mpr h'))]

theorem β_le_one {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (i j : Fin n) : β G x i j ≤ 1 := by
  unfold β; split <;> omega

theorem bc_le_three {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : bc G i j k x ≤ 3 := by
  have := β_le_one G x i j; have := β_le_one G x i k; have := β_le_one G x j k
  unfold bc; omega

theorem full_not_iso {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h : full G i j k x) : ¬ iso G i j k x :=
  fun h' => h'.1 h.1

theorem g_nonneg {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : 0 ≤ g G i j k x := by
  unfold g; split <;> split <;> positivity

theorem g_le_four {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : g G i j k x ≤ 4 := by
  unfold g
  have hb := bc_le_three G i j k x
  by_cases hf : full G i j k x
  · rw [if_pos hf, if_neg (full_not_iso G i j k x hf)]; norm_num
  · rw [if_neg hf]
    split
    · have : (bc G i j k x : ℤ) ≤ 3 := by exact_mod_cast hb
      nlinarith
    · norm_num

theorem g_of_full {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h : full G i j k x) : g G i j k x = 4 := by
  unfold g; rw [if_pos h, if_neg (full_not_iso G i j k x h)]; norm_num

theorem g_of_not_full_not_iso {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h1 : ¬ full G i j k x) (h2 : ¬ iso G i j k x) :
    g G i j k x = 0 := by
  unfold g; rw [if_neg h1, if_neg h2]; norm_num

theorem g_le_one {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h1 : ¬ full G i j k x) (h2 : bc G i j k x ≤ 2) :
    g G i j k x ≤ 1 := by
  unfold g; rw [if_neg h1]
  split
  · have : (bc G i j k x : ℤ) ≤ 2 := by exact_mod_cast h2
    have : (0 : ℤ) ≤ bc G i j k x := by positivity
    nlinarith
  · norm_num

theorem g_of_bc_one {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h1 : ¬ full G i j k x) (h2 : bc G i j k x = 1) :
    g G i j k x = 0 := by
  unfold g; rw [if_neg h1, h2]
  split <;> norm_num

theorem g_of_iso_three {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h1 : iso G i j k x) (h2 : bc G i j k x = 3) :
    g G i j k x = 4 := by
  unfold g
  rw [if_neg (fun h => full_not_iso G i j k x h h1), if_pos h1, h2]
  norm_num


/-! ## The corners of a block -/

-- The corner of the block of `x` (directions `i, j, k`) selected by `s`.
def rel {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) (s : Bool × Bool × Bool) : Fin n → Bool :=
  fun l => xor (x l) (xor (decide (l = i) && s.1) (xor (decide (l = j) && s.2.1) (decide (l = k) && s.2.2)))

def x3 (s t : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (xor s.1 t.1, xor s.2.1 t.2.1, xor s.2.2 t.2.2)

theorem x3_x3 (s t : Bool × Bool × Bool) : x3 s (x3 s t) = t := by
  obtain ⟨a, b, c⟩ := s; obtain ⟨a', b', c'⟩ := t
  simp [x3]

theorem x3_self (s : Bool × Bool × Bool) : x3 s s = (false, false, false) := by
  obtain ⟨a, b, c⟩ := s; simp [x3]

theorem rel_rel {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) (s t : Bool × Bool × Bool) :
    rel (rel x i j k s) i j k t = rel x i j k (x3 s t) := by
  funext l
  obtain ⟨a, b, c⟩ := s; obtain ⟨a', b', c'⟩ := t
  simp only [rel, x3, Bool.and_xor_distrib_left, Bool.xor_assoc, Bool.xor_left_comm]

theorem rel_zero {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) :
    rel x i j k (false, false, false) = x := by
  funext l; simp [rel]

theorem rel_rel_self {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) (s : Bool × Bool × Bool) :
    rel (rel x i j k s) i j k s = x := by
  rw [rel_rel, x3_self, rel_zero]

-- Reindexing a sum over the block by an involution of the corners.
theorem sum_rel_rebase {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) (s₀ : Bool × Bool × Bool)
    (F : (Fin n → Bool) → ℤ) :
    ∑ s, F (rel (rel x i j k s₀) i j k s) = ∑ s, F (rel x i j k s) := by
  have hinv : Function.Involutive (x3 s₀) := fun t => x3_x3 s₀ t
  refine Fintype.sum_equiv hinv.toPerm _ _ fun s => ?_
  simp only [Function.Involutive.coe_toPerm, rel_rel]

theorem sum_x_rel {n : ℕ} (i j k : Fin n) (s : Bool × Bool × Bool)
    (F : (Fin n → Bool) → ℤ) :
    ∑ x : Fin n → Bool, F (rel x i j k s) = ∑ x : Fin n → Bool, F x := by
  have hinv : Function.Involutive (fun x : Fin n → Bool => rel x i j k s) :=
    fun x => rel_rel_self x i j k s
  exact Fintype.sum_equiv hinv.toPerm _ _ fun x => by
    simp only [Function.Involutive.coe_toPerm]

-- The eight corners, for distinct directions.
theorem rel_tff {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (true, false, false) = flip x i := by
  funext l; simp only [rel, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem rel_ftf {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (false, true, false) = flip x j := by
  funext l; simp only [rel, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem rel_fft {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (false, false, true) = flip x k := by
  funext l; simp only [rel, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem rel_ttf {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (true, true, false) = V002.opp x i j := by
  funext l; simp only [rel, V002.opp, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem rel_tft {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (true, false, true) = V002.opp x i k := by
  funext l; simp only [rel, V002.opp, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem rel_ftt {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (false, true, true) = V002.opp x j k := by
  funext l; simp only [rel, V002.opp, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem rel_ttt {n : ℕ} (x : Fin n → Bool) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rel x i j k (true, true, true) = flip (V002.opp x i j) k := by
  funext l; simp only [rel, V002.opp, flip_apply]
  by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;> simp_all

theorem sum_bool3 (F : Bool × Bool × Bool → ℤ) :
    ∑ s, F s = F (true, true, true) + F (true, true, false) + F (true, false, true)
      + F (true, false, false) + F (false, true, true) + F (false, true, false)
      + F (false, false, true) + F (false, false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

-- The sum over the eight corners of a block, written out.
theorem sum_block {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : Fin n → Bool) :
    ∑ s, g G i j k (rel x i j k s)
      = g G i j k (flip (V002.opp x i j) k) + g G i j k (V002.opp x i j)
        + g G i j k (V002.opp x i k) + g G i j k (flip x i) + g G i j k (V002.opp x j k)
        + g G i j k (flip x j) + g G i j k (flip x k) + g G i j k x := by
  rw [sum_bool3, rel_ttt x hij hik hjk, rel_ttf x hij hik hjk, rel_tft x hij hik hjk,
    rel_tff x hij hik hjk, rel_ftt x hij hik hjk, rel_ftf x hij hik hjk, rel_fft x hij hik hjk,
    rel_zero]


/-! ## Membership transport along flips -/

theorem mem_A_of_flip_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    {i : Fin n} {x y : Fin n → Bool} (h : flip x i = y) (hy : y ∈ V002.A G i) : x ∈ V002.A G i :=
  (mem_A_flip G i x).mp (h ▸ hy)

theorem mem_A_of_flip_eq' {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    {i : Fin n} {x y : Fin n → Bool} (h : flip x i = y) (hx : x ∈ V002.A G i) : y ∈ V002.A G i :=
  h ▸ (mem_A_flip G i x).mpr hx

theorem g_le_one' {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h1 : ¬ full G i j k x)
    (h2 : iso G i j k x → bc G i j k x ≤ 2) : g G i j k x ≤ 1 := by
  by_cases h : iso G i j k x
  · exact g_le_one G i j k x h1 (h2 h)
  · rw [g_of_not_full_not_iso G i j k x h1 h]; norm_num

theorem blue_of_bc_three {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h : bc G i j k x = 3) :
    blue G x i j ∧ blue G x i k ∧ blue G x j k := by
  unfold bc β at h
  split_ifs at h <;> simp_all

theorem bc_eq_one {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) (h1 : blue G x j k) (h2 : ¬ blue G x i j)
    (h3 : ¬ blue G x i k) : bc G i j k x = 1 := by
  simp [bc, β, h1, h2, h3]

/-! ## The four cases of the block inequality -/

-- An isolated corner with three blue pairs: the block is a hexagon plus two antipodes.
theorem block_C1 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Fin n → Bool) (hv : iso G i j k v) (hb : bc G i j k v = 3) :
    ∑ s, g G i j k (rel v i j k s) ≤ 8 := by
  obtain ⟨⟨h_ij1, h_ij2⟩, ⟨h_ik1, h_ik2⟩, ⟨h_jk1, h_jk2⟩⟩ := blue_of_bc_three G i j k v hb
  obtain ⟨hvi, hvj, hvk⟩ := hv
  rw [sum_block G hij hik hjk]
  have t0 : g G i j k v = 4 := g_of_iso_three G i j k v ⟨hvi, hvj, hvk⟩ hb
  have ti : g G i j k (flip v i) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => hvi ((mem_A_flip G i v).mp h.1))
      (fun h => h.2.1 h_ij1)
  have tj : g G i j k (flip v j) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => hvj ((mem_A_flip G j v).mp h.2.1))
      (fun h => h.1 h_ij2)
  have tk : g G i j k (flip v k) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => hvk ((mem_A_flip G k v).mp h.2.2))
      (fun h => h.1 h_ik2)
  have mij_i : V002.opp v i j ∈ V002.A G i := mem_A_of_flip_eq G (flip_opp_l v i j) h_ij2
  have mij_j : V002.opp v i j ∈ V002.A G j := mem_A_of_flip_eq G (flip_opp_r v i j) h_ij1
  have mik_i : V002.opp v i k ∈ V002.A G i := mem_A_of_flip_eq G (flip_opp_l v i k) h_ik2
  have mik_k : V002.opp v i k ∈ V002.A G k := mem_A_of_flip_eq G (flip_opp_r v i k) h_ik1
  have mjk_j : V002.opp v j k ∈ V002.A G j := mem_A_of_flip_eq G (flip_opp_l v j k) h_jk2
  have mjk_k : V002.opp v j k ∈ V002.A G k := mem_A_of_flip_eq G (flip_opp_r v j k) h_jk1
  -- the three edges at the antipode are pairwise exclusive
  have ex12 : V002.opp v j k ∈ V002.A G i → V002.opp v i k ∈ V002.A G j → False := by
    intro p1 p2
    refine not_square G hG hij h_ik2 h_jk2 ?_ ?_
    · rw [V005.flip_comm v k i]; exact p2
    · rw [V005.flip_comm v k j]; exact p1
  have ex13 : V002.opp v j k ∈ V002.A G i → V002.opp v i j ∈ V002.A G k → False := by
    intro p1 p3
    refine not_square G hG hik h_ij2 h_jk1 ?_ ?_
    · rw [V005.flip_comm v j i]; exact p3
    · exact p1
  have ex23 : V002.opp v i k ∈ V002.A G j → V002.opp v i j ∈ V002.A G k → False := by
    intro p2 p3
    exact not_square G hG hjk h_ij1 h_ik1 p3 p2
  -- the antipode's edges
  have e1 : flip (V002.opp v i j) k ∈ V002.A G i ↔ V002.opp v j k ∈ V002.A G i := by
    rw [← mem_A_flip, flip_anti_i]
  have e2 : flip (V002.opp v i j) k ∈ V002.A G j ↔ V002.opp v i k ∈ V002.A G j := by
    rw [← mem_A_flip, flip_anti_j]
  have e3 : flip (V002.opp v i j) k ∈ V002.A G k ↔ V002.opp v i j ∈ V002.A G k := by
    rw [← mem_A_flip, flip_anti_k]
  have hv4 := g_le_four G i j k (flip (V002.opp v i j) k)
  have nfull : ¬ full G i j k (flip (V002.opp v i j) k) :=
    fun h => ex12 (e1.mp h.1) (e2.mp h.2.1)
  by_cases p1 : V002.opp v j k ∈ V002.A G i
  · have np2 : V002.opp v i k ∉ V002.A G j := fun p2 => ex12 p1 p2
    have np3 : V002.opp v i j ∉ V002.A G k := fun p3 => ex13 p1 p3
    have tjk : g G i j k (V002.opp v j k) = 4 := g_of_full G i j k _ ⟨p1, mjk_j, mjk_k⟩
    have tik : g G i j k (V002.opp v i k) = 0 :=
      g_of_not_full_not_iso G i j k _ (fun h => np2 h.2.1) (fun h => h.1 mik_i)
    have tij : g G i j k (V002.opp v i j) = 0 :=
      g_of_not_full_not_iso G i j k _ (fun h => np3 h.2.2) (fun h => h.1 mij_i)
    have tv : g G i j k (flip (V002.opp v i j) k) = 0 :=
      g_of_not_full_not_iso G i j k _ nfull (fun h => h.1 (e1.mpr p1))
    linarith
  · by_cases p2 : V002.opp v i k ∈ V002.A G j
    · have np3 : V002.opp v i j ∉ V002.A G k := fun p3 => ex23 p2 p3
      have tjk : g G i j k (V002.opp v j k) = 0 :=
        g_of_not_full_not_iso G i j k _ (fun h => p1 h.1) (fun h => h.2.1 mjk_j)
      have tik : g G i j k (V002.opp v i k) = 4 := g_of_full G i j k _ ⟨mik_i, p2, mik_k⟩
      have tij : g G i j k (V002.opp v i j) = 0 :=
        g_of_not_full_not_iso G i j k _ (fun h => np3 h.2.2) (fun h => h.1 mij_i)
      have tv : g G i j k (flip (V002.opp v i j) k) = 0 :=
        g_of_not_full_not_iso G i j k _ nfull (fun h => h.2.1 (e2.mpr p2))
      linarith
    · by_cases p3 : V002.opp v i j ∈ V002.A G k
      · have tjk : g G i j k (V002.opp v j k) = 0 :=
          g_of_not_full_not_iso G i j k _ (fun h => p1 h.1) (fun h => h.2.1 mjk_j)
        have tik : g G i j k (V002.opp v i k) = 0 :=
          g_of_not_full_not_iso G i j k _ (fun h => p2 h.2.1) (fun h => h.1 mik_i)
        have tij : g G i j k (V002.opp v i j) = 4 := g_of_full G i j k _ ⟨mij_i, mij_j, p3⟩
        have tv : g G i j k (flip (V002.opp v i j) k) = 0 :=
          g_of_not_full_not_iso G i j k _ nfull (fun h => h.2.2 (e3.mpr p3))
        linarith
      · have tjk : g G i j k (V002.opp v j k) = 0 :=
          g_of_not_full_not_iso G i j k _ (fun h => p1 h.1) (fun h => h.2.1 mjk_j)
        have tik : g G i j k (V002.opp v i k) = 0 :=
          g_of_not_full_not_iso G i j k _ (fun h => p2 h.2.1) (fun h => h.1 mik_i)
        have tij : g G i j k (V002.opp v i j) = 0 :=
          g_of_not_full_not_iso G i j k _ (fun h => p3 h.2.2) (fun h => h.1 mij_i)
        linarith

-- Two adjacent full corners `y`, `flip y i`: everything else contributes nothing.
theorem block_adj {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (y : Fin n → Bool) (hy : full G i j k y) (hyi : full G i j k (flip y i)) :
    ∑ s, g G i j k (rel y i j k s) ≤ 8 := by
  obtain ⟨y_i, y_j, y_k⟩ := hy
  obtain ⟨-, yi_j, yi_k⟩ := id hyi
  rw [sum_block G hij hik hjk]
  have t0 : g G i j k y = 4 := g_of_full G i j k y ⟨y_i, y_j, y_k⟩
  have ti : g G i j k (flip y i) = 4 := g_of_full G i j k _ hyi
  have nyj_i : flip y j ∉ V002.A G i := fun h => not_square G hG hij y_i y_j yi_j h
  have nyk_i : flip y k ∉ V002.A G i := fun h => not_square G hG hik y_i y_k yi_k h
  have tj : g G i j k (flip y j) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => nyj_i h.1)
      (fun h => h.2.1 ((mem_A_flip G j y).mpr y_j))
  have tk : g G i j k (flip y k) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => nyk_i h.1)
      (fun h => h.2.2 ((mem_A_flip G k y).mpr y_k))
  have tij : g G i j k (V002.opp y i j) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => not_opp G hG hij y_i y_j h.1 h.2.1)
      (fun h => h.2.1 (mem_A_of_flip_eq G (flip_opp_r y i j) yi_j))
  have tik : g G i j k (V002.opp y i k) = 0 :=
    g_of_not_full_not_iso G i j k _ (fun h => not_opp G hG hik y_i y_k h.1 h.2.2)
      (fun h => h.2.2 (mem_A_of_flip_eq G (flip_opp_r y i k) yi_k))
  have tjk : g G i j k (V002.opp y j k) = 0 := by
    refine g_of_bc_one G i j k _ (fun h => not_opp G hG hjk y_j y_k h.2.1 h.2.2) ?_
    refine bc_eq_one G i j k _ ⟨?_, ?_⟩ ?_ ?_
    · rw [flip_opp_l]; exact (mem_A_flip G k y).mpr y_k
    · rw [flip_opp_r]; exact (mem_A_flip G j y).mpr y_j
    · intro h; have := h.2; rw [flip_opp_l] at this; exact nyk_i this
    · intro h; have := h.2; rw [flip_opp_r] at this; exact nyj_i this
  have tv : g G i j k (flip (V002.opp y i j) k) = 0 := by
    refine g_of_bc_one G i j k _ ?_ ?_
    · intro h
      have p2 : V002.opp y i k ∈ V002.A G j := mem_A_of_flip_eq' G (flip_anti_j y i j k) h.2.1
      have p3 : V002.opp y i j ∈ V002.A G k := mem_A_of_flip_eq' G (flip_anti_k y i j k) h.2.2
      exact not_square G hG hjk yi_j yi_k p3 p2
    · refine bc_eq_one G i j k _ ⟨?_, ?_⟩ ?_ ?_
      · rw [flip_anti_j]; exact mem_A_of_flip_eq G (flip_opp_r y i k) yi_k
      · rw [flip_anti_k]; exact mem_A_of_flip_eq G (flip_opp_r y i j) yi_j
      · intro h; have := h.2; rw [flip_anti_j] at this
        exact nyk_i (mem_A_of_flip_eq' G (flip_opp_l y i k) this)
      · intro h; have := h.2; rw [flip_anti_k] at this
        exact nyj_i (mem_A_of_flip_eq' G (flip_opp_l y i j) this)
  linarith

-- A full corner `y` with no full neighbour, and no isolated corner with three blue pairs.
theorem block_full_rest {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (y : Fin n → Bool) (hy : full G i j k y) (hi : ¬ full G i j k (flip y i))
    (hj : ¬ full G i j k (flip y j)) (hk : ¬ full G i j k (flip y k))
    (hno3 : ∀ s, iso G i j k (rel y i j k s) → bc G i j k (rel y i j k s) ≤ 2) :
    ∑ s, g G i j k (rel y i j k s) ≤ 8 := by
  obtain ⟨y_i, y_j, y_k⟩ := hy
  have n_ij := hno3 (true, true, false); rw [rel_ttf y hij hik hjk] at n_ij
  have n_ik := hno3 (true, false, true); rw [rel_tft y hij hik hjk] at n_ik
  have n_jk := hno3 (false, true, true); rw [rel_ftt y hij hik hjk] at n_jk
  have n_v := hno3 (true, true, true); rw [rel_ttt y hij hik hjk] at n_v
  rw [sum_block G hij hik hjk]
  have t0 : g G i j k y = 4 := g_of_full G i j k y ⟨y_i, y_j, y_k⟩
  have ti : g G i j k (flip y i) = 0 :=
    g_of_not_full_not_iso G i j k _ hi (fun h => h.1 ((mem_A_flip G i y).mpr y_i))
  have tj : g G i j k (flip y j) = 0 :=
    g_of_not_full_not_iso G i j k _ hj (fun h => h.2.1 ((mem_A_flip G j y).mpr y_j))
  have tk : g G i j k (flip y k) = 0 :=
    g_of_not_full_not_iso G i j k _ hk (fun h => h.2.2 ((mem_A_flip G k y).mpr y_k))
  have nf_ij : ¬ full G i j k (V002.opp y i j) := fun h => not_opp G hG hij y_i y_j h.1 h.2.1
  have nf_ik : ¬ full G i j k (V002.opp y i k) := fun h => not_opp G hG hik y_i y_k h.1 h.2.2
  have nf_jk : ¬ full G i j k (V002.opp y j k) := fun h => not_opp G hG hjk y_j y_k h.2.1 h.2.2
  have tij := g_le_one' G i j k _ nf_ij n_ij
  have tik := g_le_one' G i j k _ nf_ik n_ik
  have tjk := g_le_one' G i j k _ nf_jk n_jk
  by_cases hv : full G i j k (flip (V002.opp y i j) k)
  · have tv : g G i j k (flip (V002.opp y i j) k) = 4 := g_of_full G i j k _ hv
    have tjk' : g G i j k (V002.opp y j k) = 0 :=
      g_of_not_full_not_iso G i j k _ nf_jk
        (fun h => h.1 (mem_A_of_flip_eq' G (flip_anti_i y i j k) hv.1))
    have tik' : g G i j k (V002.opp y i k) = 0 :=
      g_of_not_full_not_iso G i j k _ nf_ik
        (fun h => h.2.1 (mem_A_of_flip_eq' G (flip_anti_j y i j k) hv.2.1))
    have tij' : g G i j k (V002.opp y i j) = 0 :=
      g_of_not_full_not_iso G i j k _ nf_ij
        (fun h => h.2.2 (mem_A_of_flip_eq' G (flip_anti_k y i j k) hv.2.2))
    linarith
  · have tv := g_le_one' G i j k _ hv n_v
    linarith

theorem block_no_full {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    {i j k : Fin n} (x : Fin n → Bool) (hf : ∀ s, ¬ full G i j k (rel x i j k s))
    (hno3 : ∀ s, iso G i j k (rel x i j k s) → bc G i j k (rel x i j k s) ≤ 2) :
    ∑ s, g G i j k (rel x i j k s) ≤ 8 := by
  calc ∑ s, g G i j k (rel x i j k s) ≤ ∑ _s : Bool × Bool × Bool, (1 : ℤ) :=
        Finset.sum_le_sum fun s _ => g_le_one' G i j k _ (hf s) (hno3 s)
    _ = 8 := by simp

/-! ## Permuting the three directions -/

theorem full_perm12 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : full G j i k x ↔ full G i j k x :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

theorem iso_perm12 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : iso G j i k x ↔ iso G i j k x :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

theorem bc_perm12 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : bc G j i k x = bc G i j k x := by
  unfold bc; rw [β_comm G x j i]; ring

theorem g_perm12 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : g G j i k x = g G i j k x := by
  unfold g
  simp only [full_perm12, iso_perm12, bc_perm12]

theorem full_perm23 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : full G i k j x ↔ full G i j k x :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, b, c⟩ => ⟨a, c, b⟩⟩

theorem iso_perm23 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : iso G i k j x ↔ iso G i j k x :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, b, c⟩ => ⟨a, c, b⟩⟩

theorem bc_perm23 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : bc G i k j x = bc G i j k x := by
  unfold bc; rw [β_comm G x k j]; ring

theorem g_perm23 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) : g G i k j x = g G i j k x := by
  unfold g
  simp only [full_perm23, iso_perm23, bc_perm23]

def sw12 (s : Bool × Bool × Bool) : Bool × Bool × Bool := (s.2.1, s.1, s.2.2)
def sw23 (s : Bool × Bool × Bool) : Bool × Bool × Bool := (s.1, s.2.2, s.2.1)

theorem sw12_inv : Function.Involutive sw12 := fun _ => rfl
theorem sw23_inv : Function.Involutive sw23 := fun _ => rfl

theorem rel_sw12 {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) (s : Bool × Bool × Bool) :
    rel x j i k s = rel x i j k (sw12 s) := by
  funext l
  obtain ⟨a, b, c⟩ := s
  simp only [rel, sw12, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem rel_sw23 {n : ℕ} (x : Fin n → Bool) (i j k : Fin n) (s : Bool × Bool × Bool) :
    rel x i k j s = rel x i j k (sw23 s) := by
  funext l
  obtain ⟨a, b, c⟩ := s
  simp only [rel, sw23, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem sum_g_perm12 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) :
    ∑ s, g G j i k (rel x j i k s) = ∑ s, g G i j k (rel x i j k s) := by
  simp only [g_perm12]
  exact Fintype.sum_equiv sw12_inv.toPerm _ _ fun s => by
    rw [Function.Involutive.coe_toPerm, rel_sw12]

theorem sum_g_perm23 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (i j k : Fin n) (x : Fin n → Bool) :
    ∑ s, g G i k j (rel x i k j s) = ∑ s, g G i j k (rel x i j k s) := by
  simp only [g_perm23]
  exact Fintype.sum_equiv sw23_inv.toPerm _ _ fun s => by
    rw [Function.Involutive.coe_toPerm, rel_sw23]

/-! ## The block inequality and its sum over the cube -/

theorem block_le_eight {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : Fin n → Bool) : ∑ s, g G i j k (rel x i j k s) ≤ 8 := by
  by_cases h3 : ∃ s, iso G i j k (rel x i j k s) ∧ bc G i j k (rel x i j k s) = 3
  · obtain ⟨s₀, h1, h2⟩ := h3
    rw [← sum_rel_rebase x i j k s₀]
    exact block_C1 G hG hij hik hjk _ h1 h2
  · have hno3 : ∀ s, iso G i j k (rel x i j k s) → bc G i j k (rel x i j k s) ≤ 2 := by
      intro s hs
      have h := bc_le_three G i j k (rel x i j k s)
      have : bc G i j k (rel x i j k s) ≠ 3 := fun h' => h3 ⟨s, hs, h'⟩
      omega
    by_cases hf : ∃ s, full G i j k (rel x i j k s)
    · obtain ⟨s₀, hy⟩ := hf
      rw [← sum_rel_rebase x i j k s₀]
      set y := rel x i j k s₀ with hydef
      have hno3' : ∀ s, iso G i j k (rel y i j k s) → bc G i j k (rel y i j k s) ≤ 2 := by
        intro s; rw [hydef, rel_rel]; exact hno3 _
      by_cases hi : full G i j k (flip y i)
      · exact block_adj G hG hij hik hjk y hy hi
      by_cases hj : full G i j k (flip y j)
      · rw [← sum_g_perm12]
        exact block_adj G hG (Ne.symm hij) hjk hik y ((full_perm12 G i j k y).mpr hy)
          ((full_perm12 G i j k _).mpr hj)
      by_cases hk : full G i j k (flip y k)
      · rw [← sum_g_perm23, ← sum_g_perm12]
        exact block_adj G hG (Ne.symm hik) (Ne.symm hjk) hij y
          ((full_perm12 G i k j y).mpr ((full_perm23 G i j k y).mpr hy))
          ((full_perm12 G i k j _).mpr ((full_perm23 G i j k _).mpr hk))
      exact block_full_rest G hG hij hik hjk y hy hi hj hk hno3'
    · exact block_no_full G x (fun s hs => hf ⟨s, hs⟩) hno3

theorem sum_g_le {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : ¬ HasSquare G) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ x : Fin n → Bool, g G i j k x ≤ 2 ^ n := by
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have h8 : (8 : ℤ) * ∑ x : Fin n → Bool, g G i j k x
      = ∑ x : Fin n → Bool, ∑ s, g G i j k (rel x i j k s) := by
    rw [Finset.sum_comm]
    simp only [sum_x_rel, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool]
    ring
  have hle : ∑ x : Fin n → Bool, ∑ s, g G i j k (rel x i j k s)
      ≤ ∑ _x : Fin n → Bool, (8 : ℤ) :=
    Finset.sum_le_sum fun x _ => block_le_eight G hG hij hik hjk x
  rw [Finset.sum_const, Finset.card_univ, hcard] at hle
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  linarith


/-! ## Summing the block inequality over ordered triples of directions -/

-- The directions present and missing at `x`.
def D {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => x ∈ V002.A G i)

def M {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => x ∉ V002.A G i)

theorem card_D {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (x : Fin n → Bool) : #(D G x) = G.degree x := by
  rw [V002.degree_eq' G hle x]
  congr 1; ext i; simp [D, V005.mem_A]

theorem card_M {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (x : Fin n → Bool) : #(M G x) = n - G.degree x := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => x ∈ V002.A G i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 := card_D G hle x
  unfold M; unfold D at h2
  omega

-- Nested sums over distinct triples of a filtered set.
theorem sum_nested_filter {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (F : α → α → α → ℤ) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, ∑ k ∈ (s.erase i).erase j, (if p i ∧ p j ∧ p k then F i j k else 0)
      = ∑ i ∈ s.filter p, ∑ j ∈ (s.filter p).erase i, ∑ k ∈ ((s.filter p).erase i).erase j,
          F i j k := by
  simp only [← Finset.filter_erase, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : p i
  · simp only [hi, true_and, if_true]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : p j
    · simp only [hj, true_and, if_true]
    · simp [hj]
  · simp [hi]

-- The number of ordered triples of distinct elements.
theorem sum_triples_const {α : Type*} [DecidableEq α] (s : Finset α) (c : ℤ) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, ∑ k ∈ (s.erase i).erase j, c
      = ((#s * (#s - 1) * (#s - 2) : ℕ) : ℤ) * c := by
  have h1 : ∀ i ∈ s, ∀ j ∈ s.erase i, #((s.erase i).erase j) = #s - 2 := by
    intro i hi j hj
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega
  calc ∑ i ∈ s, ∑ j ∈ s.erase i, ∑ k ∈ (s.erase i).erase j, c
      = ∑ i ∈ s, ∑ j ∈ s.erase i, ((#s - 2 : ℕ) : ℤ) * c := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.sum_const, h1 i hi j hj, nsmul_eq_mul]
    _ = ∑ i ∈ s, ((#s - 1 : ℕ) : ℤ) * (((#s - 2 : ℕ) : ℤ) * c) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
    _ = ((#s * (#s - 1) * (#s - 2) : ℕ) : ℤ) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring

-- The triple sum of the block weight at a fixed word.
theorem sum_g_triples {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, g G i j k x
      = 4 * ((#(D G x) * (#(D G x) - 1) * (#(D G x) - 2) : ℕ) : ℤ)
        + ∑ i ∈ M G x, ∑ j ∈ (M G x).erase i, ∑ k ∈ ((M G x).erase i).erase j,
            ((bc G i j k x : ℤ) - 1) ^ 2 := by
  simp only [g, full, iso, Finset.sum_add_distrib]
  congr 1
  · rw [sum_nested_filter Finset.univ (fun i => x ∈ V002.A G i) (fun _ _ _ => (4 : ℤ))]
    rw [sum_triples_const]
    unfold D; ring
  · exact sum_nested_filter Finset.univ (fun i => ¬ x ∈ V002.A G i)
      (fun i j k => ((bc G i j k x : ℤ) - 1) ^ 2)

/-! ## The auxiliary graph of blue pairs at a word -/

theorem triple_identity (a b c : ℤ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) :
    2 * (a + b + c - 1) ^ 2
      = 2 + (2 * (a + b) ^ 2 - 3 * (a + b)) + (2 * (a + c) ^ 2 - 3 * (a + c))
        + (2 * (b + c) ^ 2 - 3 * (b + c)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num

-- `Σ_{j ≠ k} (2(β_j + β_k)² − 3(β_j + β_k)) = 4r² − 2(t + 1)r` for a 0/1 vector with sum `r`.
theorem sum_pairs {α : Type*} [DecidableEq α] (s : Finset α) (β : α → ℤ)
    (hβ : ∀ j, β j = 0 ∨ β j = 1) :
    ∑ j ∈ s, ∑ k ∈ s.erase j, (2 * (β j + β k) ^ 2 - 3 * (β j + β k))
      = 4 * (∑ j ∈ s, β j) ^ 2 - 2 * (#s : ℤ) * (∑ j ∈ s, β j) - 2 * ∑ j ∈ s, β j := by
  have hsq : ∀ j, β j ^ 2 = β j := fun j => by rcases hβ j with h | h <;> simp [h]
  have hpt : ∀ j k, 2 * (β j + β k) ^ 2 - 3 * (β j + β k) = 4 * (β j * β k) - β j - β k := by
    intro j k
    have h1 := hsq j; have h2 := hsq k
    linear_combination 2 * h1 + 2 * h2
  simp only [hpt]
  have herase : ∀ j ∈ s, ∑ k ∈ s.erase j, (4 * (β j * β k) - β j - β k)
      = (∑ k ∈ s, (4 * (β j * β k) - β j - β k)) - (4 * (β j * β j) - β j - β j) :=
    fun j hj => Finset.sum_erase_eq_sub hj
  rw [Finset.sum_congr rfl herase]
  have hjj : ∀ j, 4 * (β j * β j) - β j - β j = 2 * β j := by
    intro j; have := hsq j; linear_combination 4 * this
  simp only [hjj, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

theorem swap_outer {α : Type*} [DecidableEq α] (s : Finset α) (F : α → α → ℤ) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, F i j = ∑ j ∈ s, ∑ i ∈ s.erase j, F i j := by
  refine Finset.sum_comm' fun i j => ?_
  simp only [Finset.mem_erase]
  tauto

theorem aux_bound {α : Type*} [DecidableEq α] (M : Finset α) (β : α → α → ℤ)
    (hβ : ∀ i j, β i j = 0 ∨ β i j = 1) (hs : ∀ i j, β i j = β j i) :
    8 * ((#M * (#M - 1) * (#M - 2) : ℕ) : ℤ)
      ≤ 8 * (∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
          (β i j + β i k + β j k - 1) ^ 2) + 3 * (#M : ℤ) ^ 3 := by
  set t : ℤ := (#M : ℤ) with ht
  -- the blue degrees
  set r : α → ℤ := fun i => ∑ j ∈ M.erase i, β i j with hr
  have hcard : ∀ i ∈ M, ((#(M.erase i) : ℕ) : ℤ) = t - 1 := by
    intro i hi
    rw [Finset.card_erase_of_mem hi, Nat.cast_pred (Finset.card_pos.mpr ⟨i, hi⟩)]
  -- the three pair sums
  have hT1 : ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
      (2 * (β i j + β i k) ^ 2 - 3 * (β i j + β i k)) = ∑ i ∈ M, (4 * r i ^ 2 - 2 * t * r i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [sum_pairs (M.erase i) (fun j => β i j) (fun j => hβ i j), hcard i hi]
    ring
  have hT2 : ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
      (2 * (β i j + β j k) ^ 2 - 3 * (β i j + β j k)) = ∑ i ∈ M, (4 * r i ^ 2 - 2 * t * r i) := by
    rw [swap_outer]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : ∀ i ∈ M.erase j, ∑ k ∈ (M.erase i).erase j, (2 * (β i j + β j k) ^ 2 - 3 * (β i j + β j k))
        = ∑ k ∈ (M.erase j).erase i, (2 * (β j i + β j k) ^ 2 - 3 * (β j i + β j k)) := by
      intro i _
      rw [Finset.erase_right_comm, hs i j]
    rw [Finset.sum_congr rfl this, sum_pairs (M.erase j) (fun i => β j i) (fun i => hβ j i),
      hcard j hj]
    ring
  have hT3 : ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
      (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k)) = ∑ i ∈ M, (4 * r i ^ 2 - 2 * t * r i) := by
    have hin : ∀ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
        (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k))
        = ∑ k ∈ M.erase i, ∑ j ∈ (M.erase i).erase k,
            (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k)) := by
      intro i _
      exact swap_outer (M.erase i) (fun j k => 2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k))
    rw [Finset.sum_congr rfl hin, swap_outer]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : ∀ i ∈ M.erase k, ∑ j ∈ (M.erase i).erase k, (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k))
        = ∑ j ∈ (M.erase k).erase i, (2 * (β k i + β k j) ^ 2 - 3 * (β k i + β k j)) := by
      intro i _
      rw [Finset.erase_right_comm, hs i k]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hs j k]
    rw [Finset.sum_congr rfl this, sum_pairs (M.erase k) (fun i => β k i) (fun i => hβ k i),
      hcard k hk]
    ring
  -- the identity for the triple sum
  have hpt : ∀ i ∈ M, ∀ j ∈ M.erase i, ∀ k ∈ (M.erase i).erase j,
      2 * (β i j + β i k + β j k - 1) ^ 2
        = 2 + (2 * (β i j + β i k) ^ 2 - 3 * (β i j + β i k))
          + (2 * (β i j + β j k) ^ 2 - 3 * (β i j + β j k))
          + (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k)) :=
    fun i _ j _ k _ => triple_identity _ _ _ (hβ i j) (hβ i k) (hβ j k)
  have hid : 2 * ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
      (β i j + β i k + β j k - 1) ^ 2
      = 2 * ((#M * (#M - 1) * (#M - 2) : ℕ) : ℤ) + 3 * ∑ i ∈ M, (4 * r i ^ 2 - 2 * t * r i) := by
    calc 2 * ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
          (β i j + β i k + β j k - 1) ^ 2
        = ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
            2 * (β i j + β i k + β j k - 1) ^ 2 := by
          simp only [Finset.mul_sum]
      _ = ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
            (2 + (2 * (β i j + β i k) ^ 2 - 3 * (β i j + β i k))
              + (2 * (β i j + β j k) ^ 2 - 3 * (β i j + β j k))
              + (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k))) :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
            Finset.sum_congr rfl fun k hk => hpt i hi j hj k hk
      _ = (∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j, (2 : ℤ))
          + ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
              (2 * (β i j + β i k) ^ 2 - 3 * (β i j + β i k))
          + ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
              (2 * (β i j + β j k) ^ 2 - 3 * (β i j + β j k))
          + ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
              (2 * (β i k + β j k) ^ 2 - 3 * (β i k + β j k)) := by
          simp only [Finset.sum_add_distrib]
      _ = 2 * ((#M * (#M - 1) * (#M - 2) : ℕ) : ℤ)
          + 3 * ∑ i ∈ M, (4 * r i ^ 2 - 2 * t * r i) := by
          rw [hT1, hT2, hT3, sum_triples_const]; ring
  -- `16 r² − 8 t r ≥ −t²`
  have hsq : ∀ i ∈ M, -(t ^ 2) ≤ 16 * r i ^ 2 - 8 * t * r i := by
    intro i _
    nlinarith [sq_nonneg (4 * r i - t)]
  have hsum := Finset.sum_le_sum hsq
  rw [Finset.sum_const, nsmul_eq_mul, ← ht] at hsum
  have e : ∑ i ∈ M, (16 * r i ^ 2 - 8 * t * r i) = 4 * ∑ i ∈ M, (4 * r i ^ 2 - 2 * t * r i) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have h8 : 8 * ∑ i ∈ M, ∑ j ∈ M.erase i, ∑ k ∈ (M.erase i).erase j,
      (β i j + β i k + β j k - 1) ^ 2
      = 8 * ((#M * (#M - 1) * (#M - 2) : ℕ) : ℤ) + 3 * ∑ i ∈ M, (16 * r i ^ 2 - 8 * t * r i) := by
    rw [e]; linarith [hid]
  rw [h8]
  nlinarith [hsum]


/-! ## The main inequality `Σ_x W(d(x), n − d(x)) ≤ 8n(n−1)(n−2)·2ⁿ` -/

theorem psi_of_lt {u : ℕ} (h : u < 4) : psi u = 0 := by
  unfold psi; rw [if_neg (by omega)]

theorem psi_cast {u : ℕ} (h : 4 ≤ u) : (psi u : ℤ) = (u : ℤ) * (5 * u - 4) * (u - 4) := by
  unfold psi
  rw [if_pos h, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 4 ≤ 5 * u), Nat.cast_sub h]
  push_cast; ring

theorem main_ineq {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hle : G ≤ hypercube n) (hG : ¬ HasSquare G) :
    ∑ x : Fin n → Bool, W (G.degree x) (n - G.degree x)
      ≤ 8 * n * (n - 1) * (n - 2) * 2 ^ n := by
  have hx : ∀ x : Fin n → Bool, (W (G.degree x) (n - G.degree x) : ℤ)
      ≤ 8 * ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
          g G i j k x := by
    intro x
    rw [sum_g_triples G x, ← card_M G hle x, ← card_D G hle x]
    have haux := aux_bound (M G x) (fun i j => (β G x i j : ℤ))
      (fun i j => by unfold β; split_ifs <;> simp) (fun i j => by simp only [β_comm G x i j])
    beta_reduce at haux
    have hbc : ∀ i j k, ((bc G i j k x : ℤ) - 1) ^ 2
        = ((β G x i j : ℤ) + (β G x i k : ℤ) + (β G x j k : ℤ) - 1) ^ 2 := by
      intro i j k; unfold bc; push_cast; ring
    simp only [hbc]
    set Q := ∑ i ∈ M G x, ∑ j ∈ (M G x).erase i, ∑ k ∈ ((M G x).erase i).erase j,
      ((β G x i j : ℤ) + (β G x i k : ℤ) + (β G x j k : ℤ) - 1) ^ 2 with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
    set t := #(M G x) with ht
    set d := #(D G x) with hd
    clear_value Q t d
    unfold W
    rcases lt_or_ge t 4 with h4 | h4
    · rw [psi_of_lt h4]; push_cast; nlinarith [hQ0]
    · push_cast
      rw [psi_cast h4]
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 4 := ⟨t - 4, by omega⟩
      have e1 : u + 4 - 1 = u + 3 := by omega
      have e2 : u + 4 - 2 = u + 2 := by omega
      rw [e1, e2] at haux
      push_cast at haux ⊢
      nlinarith [haux]
  have hsum : ∑ x : Fin n → Bool, ∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, g G i j k x
      ≤ ((n * (n - 1) * (n - 2) : ℕ) : ℤ) * 2 ^ n := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ x : Fin n → Bool, ∑ j ∈ Finset.univ.erase i,
          ∑ k ∈ (Finset.univ.erase i).erase j, g G i j k x
        = ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
            ∑ x : Fin n → Bool, g G i j k x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, (2 ^ n : ℤ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
            Finset.sum_le_sum fun k hk => ?_
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj hk
          exact sum_g_le G hG (Ne.symm hj) (Ne.symm hk.2) (Ne.symm hk.1)
      _ = ((n * (n - 1) * (n - 2) : ℕ) : ℤ) * 2 ^ n := by
          rw [sum_triples_const, Finset.card_univ, Fintype.card_fin]
  have hcast : ((∑ x : Fin n → Bool, W (G.degree x) (n - G.degree x) : ℕ) : ℤ)
      ≤ ((8 * n * (n - 1) * (n - 2) * 2 ^ n : ℕ) : ℤ) := by
    push_cast
    calc ∑ x : Fin n → Bool, (W (G.degree x) (n - G.degree x) : ℤ)
        ≤ ∑ x : Fin n → Bool, 8 * ∑ i, ∑ j ∈ Finset.univ.erase i,
            ∑ k ∈ (Finset.univ.erase i).erase j, g G i j k x :=
          Finset.sum_le_sum fun x _ => hx x
      _ = 8 * ∑ x : Fin n → Bool, ∑ i, ∑ j ∈ Finset.univ.erase i,
            ∑ k ∈ (Finset.univ.erase i).erase j, g G i j k x := by rw [Finset.mul_sum]
      _ ≤ 8 * (((n * (n - 1) * (n - 2) : ℕ) : ℤ) * 2 ^ n) := by linarith [hsum]
      _ = 8 * (n : ℤ) * ((n - 1 : ℕ) : ℤ) * ((n - 2 : ℕ) : ℤ) * 2 ^ n := by push_cast; ring
  exact_mod_cast hcast

/-! ## Convexity of the weight and the secant bound -/

theorem cast_cub (d : ℕ) :
    ((32 * d * (d - 1) * (d - 2) : ℕ) : ℤ) = 32 * (d : ℤ) * ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
  rcases d with _ | _ | d
  · simp
  · simp
  · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d + 1 + 1),
      Nat.cast_sub (by omega : 2 ≤ d + 1 + 1)]
    push_cast; ring

theorem cubic_convex (k : ℕ) :
    2 * (32 * (k + 1) * (k + 1 - 1) * (k + 1 - 2))
      ≤ 32 * k * (k - 1) * (k - 2) + 32 * (k + 1 + 1) * (k + 1 + 1 - 1) * (k + 1 + 1 - 2) := by
  have h1 := cast_cub (k + 1); have h2 := cast_cub k; have h3 := cast_cub (k + 1 + 1)
  have : ((2 * (32 * (k + 1) * (k + 1 - 1) * (k + 1 - 2)) : ℕ) : ℤ)
      ≤ ((32 * k * (k - 1) * (k - 2) + 32 * (k + 1 + 1) * (k + 1 + 1 - 1) * (k + 1 + 1 - 2) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_add, h1, h2, h3]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℤ) k]
  exact_mod_cast this

theorem psi_convex (t : ℕ) : 2 * psi (t + 1) ≤ psi t + psi (t + 1 + 1) := by
  rcases lt_or_ge t 3 with h | h
  · rw [psi_of_lt (by omega : t + 1 < 4)]; omega
  · rcases eq_or_lt_of_le h with h3 | h4
    · subst h3; decide
    · have p0 := psi_cast (by omega : 4 ≤ t)
      have p1 := psi_cast (by omega : 4 ≤ t + 1)
      have p2 := psi_cast (by omega : 4 ≤ t + 1 + 1)
      have ht : (4 : ℤ) ≤ t := by exact_mod_cast (by omega : 4 ≤ t)
      have : ((2 * psi (t + 1) : ℕ) : ℤ) ≤ ((psi t + psi (t + 1 + 1) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_add, p0, p1, p2]
        push_cast
        nlinarith
      exact_mod_cast this

theorem f_convex (n k : ℕ) :
    2 * W (k + 1) (n - (k + 1)) ≤ W k (n - k) + W (k + 1 + 1) (n - (k + 1 + 1)) := by
  unfold W
  have h1 := cubic_convex k
  have h2 : 2 * psi (n - (k + 1)) ≤ psi (n - k) + psi (n - (k + 1 + 1)) := by
    rcases lt_or_ge n (k + 2) with h | h
    · have e : n - (k + 1) = 0 := by omega
      rw [e, psi_of_lt (by norm_num)]; omega
    · obtain ⟨u, hu⟩ : ∃ u, n = u + (k + 1 + 1) := ⟨n - (k + 2), by omega⟩
      have e0 : n - k = u + 1 + 1 := by omega
      have e1 : n - (k + 1) = u + 1 := by omega
      have e2 : n - (k + 1 + 1) = u := by omega
      rw [e0, e1, e2]
      have := psi_convex u
      omega
  omega

theorem slope_mono (f : ℕ → ℕ) (hf : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 1 + 1)) :
    ∀ c d, c ≤ d → f d + f (c + 1) ≤ f c + f (d + 1) := by
  intro c d hcd
  induction d, hcd using Nat.le_induction with
  | base => omega
  | succ d _ ih => have := hf d; omega

theorem slope_mono' (f : ℕ → ℕ) (hf : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 1 + 1)) :
    ∀ e d, f (d + 1) + f (d + e) ≤ f d + f (d + e + 1) := by
  intro e
  induction e with
  | zero => intro d; simp only [Nat.add_zero]; omega
  | succ e ih =>
    intro d
    have h1 := ih (d + 1)
    have h2 := hf d
    have e1 : d + (e + 1) = d + 1 + e := by omega
    rw [e1]
    omega

-- A convex sequence lies above its secants: `f c + s·d ≤ f d + s·c` with `s = f (c+1) − f c`.
theorem secant (f : ℕ → ℕ) (hf : ∀ k, 2 * f (k + 1) ≤ f k + f (k + 1 + 1)) (c : ℕ)
    (hc : f c ≤ f (c + 1)) (d : ℕ) :
    f c + (f (c + 1) - f c) * d ≤ f d + (f (c + 1) - f c) * c := by
  rcases le_or_gt c d with hcd | hdc
  · induction d, hcd using Nat.le_induction with
    | base => omega
    | succ d hcd ih =>
      have := slope_mono f hf c d hcd
      rw [Nat.mul_succ]; omega
  · have key : ∀ e d, d + e = c →
        f c + (f (c + 1) - f c) * d ≤ f d + (f (c + 1) - f c) * c := by
      intro e
      induction e with
      | zero => intro d hd; simp only [Nat.add_zero] at hd; subst hd; omega
      | succ e ih =>
        intro d hd
        have h1 := ih (d + 1) (by omega)
        have h2 := slope_mono' f hf (e + 1) d
        rw [hd] at h2
        rw [Nat.mul_succ] at h1
        omega
    obtain ⟨e, he⟩ : ∃ e, d + e = c := ⟨c - d, by omega⟩
    exact key e d he

/-! ## The bound -/

theorem main {n : ℕ} (hn : 1 ≤ n) (c : ℕ) : SqueezeBench.HypercubeC4.f n ≤ bound n c := by
  unfold bound
  split_ifs with hs
  · refine f_le_of_forall_not_hasSquare (by rw [nMin_eq]; omega) fun G _ hle hG => ?_
    have hmain := main_ineq G hle hG
    have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
    have hD : slope n c = W (c + 1) (n - (c + 1)) - W c (n - c) := by
      unfold slope; rw [Nat.sub_sub]
    have hc : W c (n - c) ≤ W (c + 1) (n - (c + 1)) := by rw [hD] at hs; omega
    have hsec : ∀ d, W c (n - c) + slope n c * d ≤ W d (n - d) + slope n c * c := by
      intro d
      have h := secant (fun k => W k (n - k)) (f_convex n) c hc d
      beta_reduce at h
      rwa [← hD] at h
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset (Fin n → Bool))) =>
      hsec (G.degree x)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum, SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.card_univ, hcard,
      smul_eq_mul, smul_eq_mul] at hsum
    rw [Nat.le_div_iff_mul_le hs]
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; ring
    rw [h2n] at hsum hmain
    set D := slope n c
    set m := #G.edgeFinset
    set Wc := W c (n - c)
    set P := 8 * n * (n - 1) * (n - 2)
    set S := ∑ x : Fin n → Bool, W (G.degree x) (n - G.degree x)
    set T := 2 ^ (n - 1) with hTdef
    have hT : 0 < T := by rw [hTdef]; positivity
    clear_value D m Wc P S T
    have hWc : Wc ≤ P + c * D := by
      have : 2 * T * Wc ≤ 2 * T * (P + c * D) := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have hX := Nat.sub_add_cancel hWc
    set X := P + c * D - Wc
    clear_value X
    have hX2 : T * X + T * Wc = T * (P + c * D) := by rw [← Nat.mul_add, hX]
    have : 2 * (m * D) ≤ 2 * (T * X) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by norm_num)
  · exact V001.valid n

-- Each `bound n c` is a bound, so their minimum is.
theorem le_best {n X : ℕ} (h : ∀ c, X ≤ bound n c) : ∀ k, X ≤ best n k
  | 0 => h 2
  | k + 1 => le_min (le_best h k) (h (k + 3))

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f v := by
  intro n
  by_cases hn : 1 ≤ n
  · exact le_best (fun c => main hn c) n
  · have h0 : n = 0 := by omega
    subst h0
    exact (V006.valid 0).trans (by decide)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.minWith_valid SqueezeBench.HypercubeC4.Upper.V006.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V006.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V006.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.HypercubeC4.nMin) (n₀ := 12) (by decide) (by decide)

end SqueezeBench.HypercubeC4.Upper.V007
