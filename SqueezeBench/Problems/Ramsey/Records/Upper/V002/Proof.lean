import SqueezeBench.Problems.Ramsey.Records.Upper.V002.Def
import SqueezeBench.Problems.Ramsey.Records.Upper.V001.Proof

/-! Record V002 for Ramsey, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Upper/V002.lean`.

The new ingredient is `forcesOn_walker`, the counting bound of Walker (1968) in the
off-diagonal form of Li–Rousseau–Zang (2004). Let `G` be a graph on `V = x + 1` vertices with
no `K_{s+2}` and no independent set of size `t+2`. Adjacent pairs have fewer than
`A = R(s, t+2)` common neighbours (`codeg_adj_lt`), and non-adjacent pairs fewer than
`C = R(s+2, t)` common non-neighbours (`commonNon_lt`), so by inclusion–exclusion a
non-adjacent pair has at most `deg u + deg v + C + 1 - V` common neighbours. Counting paths
of length two from both ends (`sum_codeg`) gives
`3·Σ deg² ≤ (A - C + 3V - 3)·Σ deg - (V - C - 1)·V·(V - 1)`, which by Cauchy–Schwarz has no
solution when `3x² > 6x(A+C) + (A-C)²` (`walker_arith`). The Erdős–Szekeres step and its
parity saving are reused from V001. -/

namespace SqueezeBench.Ramsey.Upper.V002

open SqueezeBench SimpleGraph Finset

theorem walker_arith {A C V x D S N Xa Xb Sdn : ℕ}
    (hV : V = x + 1)
    (h1 : S = Xa + Xb + D)
    (h2 : Xa + D ≤ A * D)
    (h3 : Xb + V * N ≤ 2 * Sdn + (C + 1) * N)
    (h4 : Sdn + S + D = V * D)
    (h5 : N + D + V = V * V)
    (h6 : D * D ≤ V * S)
    (hx : 6 * x * (A + C) + A * A + C * C < 3 * x * x + 2 * A * C) : False := by
  subst hV
  zify at *
  have hN : (N:ℤ) = (x + 1) * (x + 1) - D - (x + 1) := by linarith
  have hS : (Sdn:ℤ) = (x + 1) * D - S - D := by linarith
  rw [hN, hS] at h3
  have k1 : 3 * (S:ℤ) ≤ (A + 3 * x - C) * D - x * (x - C) * (x + 1) := by linarith
  have k2 : (x + 1 : ℤ) * (3 * S) ≤ (x + 1) * ((A + 3 * x - C) * D - x * (x - C) * (x + 1)) :=
    mul_le_mul_of_nonneg_left k1 (by positivity)
  have key : 12 * (3 * (D:ℤ) * D - (x + 1) * ((A + 3 * x - C) * D - x * (x - C) * (x + 1)))
      = (6 * D - (A + 3 * x - C) * (x + 1)) ^ 2
        + (x + 1) ^ 2 * (3 * x * x + 2 * A * C - (6 * x * (A + C) + A * A + C * C)) := by
    ring
  have pos : 0 < ((x:ℤ) + 1) ^ 2 * (3 * x * x + 2 * A * C - (6 * x * (A + C) + A * A + C * C)) :=
    mul_pos (by positivity) (by linarith)
  have sq := sq_nonneg (6 * (D:ℤ) - (A + 3 * x - C) * (x + 1))
  linarith

theorem crit_mono {A C x x' : ℕ} (hx : 6 * x * (A + C) + A * A + C * C < 3 * x * x + 2 * A * C)
    (h : x ≤ x') : 6 * x' * (A + C) + A * A + C * C < 3 * x' * x' + 2 * A * C := by
  have h2 : 2 * (A + C) < x := by
    by_contra hc
    push Not at hc
    nlinarith [sq_nonneg (A - C : ℤ), Nat.mul_le_mul_right x hc]
  nlinarith [Nat.mul_le_mul h h, Nat.mul_le_mul_left (A + C) h]

-- Adjacent vertices have fewer than `A` common neighbours when `A` forces `(s, t+2)`.
theorem codeg_adj_lt {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {A s t : ℕ} (hA : ForcesOn A s (t + 2))
    (hG : ∀ S : Finset V, ¬ G.IsNClique (s + 2) S) (hG' : ∀ T : Finset V, ¬ Gᶜ.IsNClique (t + 2) T)
    {u v : V} (huv : G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card < A := by
  by_contra h
  push Not at h
  set X : Finset V := G.neighborFinset u ∩ G.neighborFinset v with hX
  have hcardX : A ≤ Fintype.card ((X : Finset V) : Set V) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]; exact h
  rcases hA (G.induce ((X : Finset V) : Set V)) hcardX with ⟨S, hS⟩ | ⟨T, hT⟩
  · rw [isNClique_induce_iff] at hS
    have hsub : ∀ b ∈ S.map (Function.Embedding.subtype _), b ∈ X := by
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨w, _, rfl⟩ := hb
      exact w.2
    have h1 : G.IsNClique (s + 1) (insert v (S.map (Function.Embedding.subtype _))) := by
      refine hS.insert ?_
      intro b hb
      have := hsub b hb
      rw [hX, Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at this
      exact this.2
    have h2 : G.IsNClique (s + 2) (insert u (insert v (S.map (Function.Embedding.subtype _)))) := by
      refine h1.insert ?_
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact huv
      · have := hsub b hb
        rw [hX, Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at this
        exact this.1
    exact hG _ h2
  · rw [← induce_compl, isNClique_induce_iff] at hT
    exact hG' _ hT

-- The common non-neighbours of a non-adjacent pair.
def commonNon {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Finset V :=
  ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).erase u).erase v

theorem mem_commonNon {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v w : V} :
    w ∈ commonNon G u v ↔ w ≠ v ∧ w ≠ u ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w := by
  simp [commonNon]

-- A non-adjacent pair has fewer than `C` common non-neighbours when `C` forces `(s+2, t)`.
theorem commonNon_lt {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {C s t : ℕ} (hC : ForcesOn C (s + 2) t)
    (hG : ∀ S : Finset V, ¬ G.IsNClique (s + 2) S) (hG' : ∀ T : Finset V, ¬ Gᶜ.IsNClique (t + 2) T)
    {u v : V} (hne : u ≠ v) (huv : ¬ G.Adj u v) :
    (commonNon G u v).card < C := by
  by_contra h
  push Not at h
  set X : Finset V := commonNon G u v with hX
  have hcardX : C ≤ Fintype.card ((X : Finset V) : Set V) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]; exact h
  rcases hC (G.induce ((X : Finset V) : Set V)) hcardX with ⟨S, hS⟩ | ⟨T, hT⟩
  · rw [isNClique_induce_iff] at hS
    exact hG _ hS
  · rw [← induce_compl, isNClique_induce_iff] at hT
    have hsub : ∀ b ∈ T.map (Function.Embedding.subtype _), b ∈ X := by
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨w, _, rfl⟩ := hb
      exact w.2
    have h1 : Gᶜ.IsNClique (t + 1) (insert v (T.map (Function.Embedding.subtype _))) := by
      refine hT.insert ?_
      intro b hb
      have := (mem_commonNon G).mp (hsub b hb)
      rw [compl_adj]
      exact ⟨fun hvb => this.1 hvb.symm, this.2.2.2⟩
    have h2 : Gᶜ.IsNClique (t + 2) (insert u (insert v (T.map (Function.Embedding.subtype _)))) := by
      refine h1.insert ?_
      intro b hb
      rw [Finset.mem_insert] at hb
      rw [compl_adj]
      rcases hb with rfl | hb
      · exact ⟨hne, huv⟩
      · have := (mem_commonNon G).mp (hsub b hb)
        exact ⟨fun hub => this.2.1 hub.symm, this.2.2.1⟩
    exact hG' _ h2

-- Inclusion–exclusion for a non-adjacent pair: `codeg + V = deg u + deg v + |commonNon| + 2`.
theorem codeg_nonadj_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (hne : u ≠ v) (huv : ¬ G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card + Fintype.card V =
      G.degree u + G.degree v + (commonNon G u v).card + 2 := by
  have hu : u ∉ G.neighborFinset u ∪ G.neighborFinset v := by
    simp only [Finset.mem_union, mem_neighborFinset, not_or]
    exact ⟨G.irrefl, fun h => huv h.symm⟩
  have hv : v ∉ G.neighborFinset u ∪ G.neighborFinset v := by
    simp only [Finset.mem_union, mem_neighborFinset, not_or]
    exact ⟨huv, G.irrefl⟩
  have hu' : u ∈ Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v) := by simp [hu]
  have hv' : v ∈ (Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).erase u := by
    simp [hv, hne.symm]
  have h1 : (commonNon G u v).card + 2 =
      (Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card := by
    unfold commonNon
    rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu']
    have h2 : 1 ≤ ((Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).erase u).card :=
      Finset.card_pos.mpr ⟨v, hv'⟩
    have h3 := Finset.card_erase_of_mem hu'
    have h4 : 1 ≤ (Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card :=
      Finset.card_pos.mpr ⟨u, hu'⟩
    omega
  have h2 : (Finset.univ \ (G.neighborFinset u ∪ G.neighborFinset v)).card +
      (G.neighborFinset u ∪ G.neighborFinset v).card = Fintype.card V := by
    rw [Finset.card_univ_sdiff]
    have := Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
    omega
  have h3 := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  simp only [card_neighborFinset_eq_degree] at h3
  omega

-- The number of common neighbours as an indicator sum.
theorem codeg_eq_sum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) :
    (G.neighborFinset u ∩ G.neighborFinset v).card =
      ∑ w, (if G.Adj u w then 1 else 0) * (if G.Adj v w then 1 else 0) := by
  have : G.neighborFinset u ∩ G.neighborFinset v =
      Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
    ext w; simp
  rw [this, Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro w _
  split_ifs <;> simp_all

theorem degree_eq_sum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) :
    G.degree u = ∑ w, (if G.Adj u w then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

-- Paths of length two counted from both ends: `∑ u v, codeg u v = ∑ w, deg w ^ 2`.
theorem sum_codeg {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∑ u, ∑ v, (G.neighborFinset u ∩ G.neighborFinset v).card = ∑ w, G.degree w * G.degree w := by
  simp only [codeg_eq_sum]
  rw [Finset.sum_comm]
  -- now ∑ v, ∑ u, ∑ w, ...
  have : ∀ v : V, ∑ u, ∑ w, (if G.Adj u w then 1 else 0) * (if G.Adj v w then 1 else 0)
      = ∑ w, ∑ u, (if G.Adj u w then 1 else 0) * (if G.Adj v w then 1 else 0) := by
    intro v; exact Finset.sum_comm
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro w _
  have h : ∀ x : V, (if G.Adj x w then 1 else 0 : ℕ) = if G.Adj w x then 1 else 0 := by
    intro x; simp only [G.adj_comm]
  simp only [h, ← Finset.sum_mul, ← Finset.mul_sum, ← degree_eq_sum, mul_comm]

-- The main counting lemma.
theorem forcesOn_walker {A C s t x : ℕ}
    (hA : ForcesOn A s (t + 2)) (hC : ForcesOn C (s + 2) t)
    (hx : 6 * x * (A + C) + A * A + C * C < 3 * x * x + 2 * A * C) :
    ForcesOn (x + 1) (s + 2) (t + 2) := by
  intro V _ _ G hcard
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hG, hG'⟩ := hcon
  -- the criterion at the actual vertex count
  have hx' : 6 * (Fintype.card V - 1) * (A + C) + A * A + C * C
      < 3 * (Fintype.card V - 1) * (Fintype.card V - 1) + 2 * A * C :=
    crit_mono hx (by omega)
  set n := Fintype.card V with hn
  -- indicators
  let a : V → V → ℕ := fun u v => if G.Adj u v then 1 else 0
  let b : V → V → ℕ := fun u v => if v ≠ u ∧ ¬ G.Adj u v then 1 else 0
  let e : V → V → ℕ := fun u v => if v = u then 1 else 0
  let cd : V → V → ℕ := fun u v => (G.neighborFinset u ∩ G.neighborFinset v).card
  have hsplit : ∀ u v, e u v + a u v + b u v = 1 := by
    intro u v
    simp only [a, b, e]
    by_cases h1 : v = u
    · subst h1; simp
    · by_cases h2 : G.Adj u v <;> simp [h1, h2]
  have hb_symm : ∀ u v, b u v = b v u := by
    intro u v
    simp only [b, G.adj_comm u v, ne_comm]
  have hsum_e : ∀ u, ∑ v, e u v = 1 := by
    intro u; simp [e]
  have hsum_a : ∀ u, ∑ v, a u v = G.degree u := by
    intro u; exact (degree_eq_sum G u).symm
  have hcd_diag : ∀ u, cd u u = G.degree u := by
    intro u; simp [cd, card_neighborFinset_eq_degree]
  -- the pointwise bounds
  have hadj : ∀ u v, a u v * (cd u v + 1) ≤ a u v * A := by
    intro u v
    simp only [a]
    split_ifs with h
    · have := codeg_adj_lt G hA hG hG' h
      simp only [cd]; omega
    · simp
  have hnon : ∀ u v, b u v * (cd u v + n) ≤ b u v * (G.degree u + G.degree v + C + 1) := by
    intro u v
    simp only [b]
    split_ifs with h
    · have h1 := commonNon_lt G hC hG hG' (Ne.symm h.1) h.2
      have h2 := codeg_nonadj_eq G (Ne.symm h.1) h.2
      simp only [cd, one_mul]; omega
    · simp
  -- global quantities
  set D := ∑ u, G.degree u with hD
  set S := ∑ u, G.degree u * G.degree u with hS
  set N := ∑ u, ∑ v, b u v with hN
  set Xa := ∑ u, ∑ v, a u v * cd u v with hXa
  set Xb := ∑ u, ∑ v, b u v * cd u v with hXb
  set Sdn := ∑ u, G.degree u * ∑ v, b u v with hSdn
  have h1 : S = Xa + Xb + D := by
    have := sum_codeg G
    rw [hS, ← this, hXa, hXb, hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [← Finset.sum_add_distrib]
    have : ∑ v, cd u v = ∑ v, (e u v + a u v + b u v) * cd u v := by
      refine Finset.sum_congr rfl ?_
      intro v _; rw [hsplit, one_mul]
    rw [this]
    have he : ∑ v, e u v * cd u v = G.degree u := by
      simp [e, cd, card_neighborFinset_eq_degree]
    calc ∑ v, (e u v + a u v + b u v) * cd u v
        = ∑ v, (e u v * cd u v + (a u v * cd u v + b u v * cd u v)) := by
          refine Finset.sum_congr rfl ?_; intro v _; ring
      _ = ∑ v, e u v * cd u v + ∑ v, (a u v * cd u v + b u v * cd u v) := Finset.sum_add_distrib
      _ = ∑ v, (a u v * cd u v + b u v * cd u v) + G.degree u := by rw [he, add_comm]
  have h2 : Xa + D ≤ A * D := by
    have : ∀ u, ∑ v, a u v * cd u v + G.degree u ≤ A * G.degree u := by
      intro u
      rw [← hsum_a, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum ?_
      intro v _
      have := hadj u v
      rw [mul_add, mul_one, mul_comm (a u v) A] at this
      exact this
    rw [hXa, hD, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun u _ => this u)
  have h3 : Xb + n * N ≤ 2 * Sdn + (C + 1) * N := by
    have hpt : ∀ u, ∑ v, b u v * cd u v + n * ∑ v, b u v
        ≤ G.degree u * ∑ v, b u v + ∑ v, b u v * G.degree v + (C + 1) * ∑ v, b u v := by
      intro u
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum ?_
      intro v _
      have := hnon u v
      linear_combination this
    have hswap : ∑ u, ∑ v, b u v * G.degree v = Sdn := by
      rw [hSdn, Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro v _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro u _
      rw [hb_symm, mul_comm]
    have := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hpt u)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hswap,
      ← Finset.mul_sum, ← Finset.mul_sum] at this
    rw [hXb, hN, hSdn]
    linarith [this]
  have hcount : ∀ u, ∑ v, b u v + G.degree u + 1 = n := by
    intro u
    have : ∑ v, (e u v + a u v + b u v) = n := by
      simp only [hsplit]; simp [hn]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_e, hsum_a] at this
    omega
  have h4 : Sdn + S + D = n * D := by
    rw [hSdn, hS, hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [← hcount u]
    ring
  have h5 : N + D + n = n * n := by
    have : ∑ u : V, (∑ v, b u v + G.degree u + 1) = ∑ u : V, n := by
      refine Finset.sum_congr rfl ?_; intro u _; exact hcount u
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at this
    rw [hN, hD]; rw [← hn] at this; linarith [this]
  have h6 : D * D ≤ n * S := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun u => G.degree u)
    simp only [Finset.card_univ, sq] at this
    rw [hD, hS, hn]; exact this
  have hn1 : n = (n - 1) + 1 := by omega
  exact walker_arith hn1 h1 h2 h3 h4 h5 h6 hx'

-- The Bool criterion of `Def.lean`, as a proposition.
theorem crit_iff {A C x : ℕ} :
    crit A C x = true ↔ 6 * x * (A + C) + A * A + C * C < 3 * x * x + 2 * A * C := by
  simp [crit]

theorem forcesOn_min {a b s t : ℕ} (ha : ForcesOn a s t) (hb : ForcesOn b s t) :
    ForcesOn (min a b) s t := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact ha
  · rw [min_eq_right h]; exact hb

-- Transposing the two clique sizes: pass to the complement.
theorem forcesOn_symm {N s t : ℕ} (h : ForcesOn N s t) : ForcesOn N t s := by
  intro V _ _ G hcard
  rcases h Gᶜ hcard with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact Or.inr ⟨S, hS⟩
  · rw [compl_compl] at hT
    exact Or.inl ⟨T, hT⟩

-- Whatever `walker` returns is `es` itself or a value certified by `crit`.
theorem walker_cases (A C es : ℕ) :
    walker A C es = es ∨ ∃ y, crit A C y = true ∧ walker A C es = min es (y + 1) := by
  simp only [walker]
  split_ifs with h0 h1 h2
  · exact Or.inl rfl
  · exact Or.inr ⟨_, h1, rfl⟩
  · exact Or.inr ⟨_, h2, rfl⟩
  · exact Or.inl rfl

theorem walker_forces {A C es s t : ℕ} (hA : ForcesOn A s (t + 2)) (hC : ForcesOn C (s + 2) t)
    (hes : ForcesOn es (s + 2) (t + 2)) : ForcesOn (walker A C es) (s + 2) (t + 2) := by
  rcases walker_cases A C es with h | ⟨y, hy, h⟩
  · rw [h]; exact hes
  · rw [h]
    have hw : ForcesOn (y + 1) (s + 2) (t + 2) := by
      intro V _ _
      exact forcesOn_walker hA hC (crit_iff.mp hy)
    intro V _ _
    exact forcesOn_min hes hw

theorem walker_le (A C es : ℕ) : walker A C es ≤ es := by
  rcases walker_cases A C es with h | ⟨y, _, h⟩
  · rw [h]
  · rw [h]; exact min_le_left _ _

theorem walker_pos {A C es : ℕ} (h : 1 ≤ es) : 1 ≤ walker A C es := by
  rcases walker_cases A C es with h' | ⟨y, _, h'⟩
  · rw [h']; exact h
  · rw [h']; exact le_min h (by omega)

-- The Erdős–Szekeres step with the parity saving, from V001.
theorem stepVal_forces {M N s t : ℕ} (hM : ForcesOn M s (t + 1)) (hN : ForcesOn N (s + 1) t)
    (h1 : 1 ≤ M + N) : ForcesOn (V001.stepVal M N) (s + 1) (t + 1) := by
  unfold V001.stepVal
  split
  · rename_i h
    intro V _ _
    exact V001.forcesOn_step_parity h.1 h.2 h1 hM hN
  · intro V _ _
    exact forcesOn_step h1 hM hN

theorem stepVal_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    V001.stepVal a b ≤ V001.stepVal a' b' := by
  unfold V001.stepVal
  split_ifs <;> omega

theorem stepVal_comm (a b : ℕ) : V001.stepVal a b = V001.stepVal b a := by
  unfold V001.stepVal
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;> simp [ha, hb, Nat.add_comm]

-- Mirrored reads: validity, positivity and comparison.
theorem mir_forces {f : ℕ → ℕ} {m : ℕ} (hf : ∀ j, ForcesOn (f j) j (m - j)) (j : ℕ) :
    ForcesOn (mir f m j) j (m - j) := by
  unfold mir
  split
  · rename_i h
    rcases Nat.lt_or_ge m j with hj | hj
    · rw [show m - j = 0 from by omega]
      intro V _ _
      exact forcesOn_zero_right (f 0) j
    · have h1 : ForcesOn (f (m - j)) (m - j) (m - (m - j)) := hf (m - j)
      rw [show m - (m - j) = j from by omega] at h1
      intro V _ _
      exact forcesOn_symm h1
  · intro V _ _
    exact hf j

theorem mir_pos {f : ℕ → ℕ} {m : ℕ} (hf : ∀ j, 1 ≤ j → 2 * j ≤ m → 1 ≤ f j) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j + 1 ≤ m) : 1 ≤ mir f m j := by
  unfold mir
  split
  · rename_i h
    exact hf (m - j) (by omega) (by omega)
  · rename_i h
    exact hf j h1 (by omega)

theorem mir_le {f g : ℕ → ℕ} {m : ℕ} (hf : ∀ j, f j ≤ g j) (hf0 : f 0 = 0)
    (hg : ∀ j, j ≤ m → g (m - j) = g j) (j : ℕ) : mir f m j ≤ g j := by
  unfold mir
  split
  · rename_i h
    rcases Nat.lt_or_ge m j with hj | hj
    · rw [show m - j = 0 from by omega, hf0]
      exact Nat.zero_le _
    · calc f (m - j) ≤ g (m - j) := hf _
        _ = g j := hg j hj
  · exact hf j

-- V001's table vanishes past its antidiagonal and is symmetric.
theorem v1_dRow_of_ge : ∀ k i, k + 2 ≤ i → V001.dRow k i = 0 := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i ≠ 1 := by omega
    simp [V001.dRow, this]
  | succ k ih =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [V001.dRow_succ, ih j (by omega), ih (j + 1) (by omega)]
    rfl

theorem v1_dRow_symm : ∀ k j, j ≤ k + 2 → V001.dRow k (k + 2 - j) = V001.dRow k j := by
  intro k
  induction k with
  | zero =>
    intro j hj
    interval_cases j <;> rfl
  | succ k ih =>
    intro j hj
    match j with
    | 0 =>
      rw [Nat.sub_zero, V001.dRow_zero, v1_dRow_of_ge (k + 1) (k + 1 + 2) (le_refl _)]
    | i + 1 =>
      rcases Nat.lt_or_ge (k + 1) i with hi | hi
      · have hik : i = k + 2 := by omega
        subst hik
        rw [show k + 1 + 2 - (k + 2 + 1) = 0 from by omega, V001.dRow_zero,
          v1_dRow_of_ge (k + 1) (k + 2 + 1) (by omega)]
      · rw [show k + 1 + 2 - (i + 1) = (k + 2 - (i + 1)) + 1 from by omega, V001.dRow_succ,
          V001.dRow_succ, ih (i + 1) (by omega),
          show k + 2 - (i + 1) + 1 = k + 2 - i from by omega, ih i (by omega), stepVal_comm]

theorem v1_dRow_symm' (k : ℕ) : ∀ j, j ≤ k + 3 → V001.dRow (k + 1) (k + 3 - j) = V001.dRow (k + 1) j :=
  v1_dRow_symm (k + 1)

-- The base antidiagonals agree with V001's.
theorem row0_eq (j : ℕ) : row0 j = V001.dRow 0 j := by
  simp [row0, V001.dRow]

theorem row1_succ (j : ℕ) : row1 (j + 1) = V001.stepVal (row0 j) (row0 (j + 1)) := by
  simp [row1]

theorem rows_zero_left (k : ℕ) : (rows k).1 0 = 0 := by
  cases k with
  | zero => rfl
  | succ k => rfl

-- Positivity of the interior entries.
theorem next_pos {k : ℕ} {p1 p2 : ℕ → ℕ} (h1 : ∀ j, 1 ≤ j → j ≤ k + 2 → 1 ≤ p1 j) :
    ∀ j, 1 ≤ j → j ≤ k + 3 → 1 ≤ next k p1 p2 j := by
  intro j hj1 hj2
  match j with
  | 0 => omega
  | 1 => exact le_refl 1
  | i + 2 =>
    simp only [next]
    split_ifs with hik hik'
    · apply walker_pos
      apply V001.stepVal_pos
      have hp : ∀ j, 1 ≤ j → 2 * j ≤ k + 3 → 1 ≤ p1 j := fun j hj hjm => h1 j hj (by omega)
      have := mir_pos hp (j := i + 1) (by omega) (by omega)
      omega
    · exact le_refl 1
    · omega

theorem rows_pos : ∀ k, (∀ j, 1 ≤ j → j ≤ k + 2 → 1 ≤ (rows k).1 j) ∧
    (∀ j, 1 ≤ j → j ≤ k + 1 → 1 ≤ (rows k).2 j) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro j h1 h2
      rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> decide
    · intro j h1 h2
      have : j = 1 := by omega
      subst this
      decide
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · intro j h1 h2
      show 1 ≤ next k (rows k).1 (rows k).2 j
      exact next_pos ih.1 j h1 (by omega)
    · intro j h1 h2
      show 1 ≤ (rows k).1 j
      exact ih.1 j h1 (by omega)

-- Validity of one step of the table.
theorem next_forces (k : ℕ) (p1 p2 : ℕ → ℕ)
    (h1 : ∀ j, ForcesOn (p1 j) j (k + 3 - j)) (h2 : ∀ j, ForcesOn (p2 j) j (k + 2 - j))
    (hp : ∀ j, 1 ≤ j → j ≤ k + 2 → 1 ≤ p1 j) :
    ∀ j, ForcesOn (next k p1 p2 j) j (k + 4 - j) := by
  intro j
  match j with
  | 0 =>
    show ForcesOn 0 0 (k + 4 - 0)
    intro V _ _
    exact forcesOn_zero_left 0 (k + 4 - 0)
  | 1 =>
    show ForcesOn 1 1 (k + 4 - 1)
    rw [show k + 4 - 1 = k + 3 from rfl]
    intro V _ _
    exact forcesOn_one_left (k + 3)
  | i + 2 =>
    show ForcesOn (if i ≤ k then
        walker (mir p2 (k + 2) i) (mir p2 (k + 2) (i + 2))
          (V001.stepVal (mir p1 (k + 3) (i + 1)) (mir p1 (k + 3) (i + 2)))
      else if i = k + 1 then 1 else 0) (i + 2) (k + 4 - (i + 2))
    split
    · rename_i hik
      rw [show k + 4 - (i + 2) = (k - i) + 2 from by omega]
      have hA : ForcesOn (mir p2 (k + 2) i) i (k - i + 2) := by
        have h : ForcesOn (mir p2 (k + 2) i) i (k + 2 - i) := by
          intro V _ _
          exact mir_forces h2 i
        rwa [show k + 2 - i = k - i + 2 from by omega] at h
      have hC : ForcesOn (mir p2 (k + 2) (i + 2)) (i + 2) (k - i) := by
        have h : ForcesOn (mir p2 (k + 2) (i + 2)) (i + 2) (k + 2 - (i + 2)) := by
          intro V _ _
          exact mir_forces h2 (i + 2)
        rwa [show k + 2 - (i + 2) = k - i from by omega] at h
      have hM : ForcesOn (mir p1 (k + 3) (i + 1)) (i + 1) (k - i + 1 + 1) := by
        have h : ForcesOn (mir p1 (k + 3) (i + 1)) (i + 1) (k + 3 - (i + 1)) := by
          intro V _ _
          exact mir_forces h1 (i + 1)
        rwa [show k + 3 - (i + 1) = k - i + 1 + 1 from by omega] at h
      have hN : ForcesOn (mir p1 (k + 3) (i + 2)) (i + 1 + 1) (k - i + 1) := by
        have h : ForcesOn (mir p1 (k + 3) (i + 2)) (i + 2) (k + 3 - (i + 2)) := by
          intro V _ _
          exact mir_forces h1 (i + 2)
        rwa [show k + 3 - (i + 2) = k - i + 1 from by omega] at h
      have hp' : ∀ j, 1 ≤ j → 2 * j ≤ k + 3 → 1 ≤ p1 j := fun j hj hjm => hp j hj (by omega)
      have hpos : 1 ≤ mir p1 (k + 3) (i + 1) := mir_pos hp' (by omega) (by omega)
      have hes : ForcesOn (V001.stepVal (mir p1 (k + 3) (i + 1)) (mir p1 (k + 3) (i + 2)))
          (i + 1 + 1) (k - i + 1 + 1) := by
        intro V _ _
        exact stepVal_forces hM hN (by omega)
      intro V _ _
      exact walker_forces hA hC hes
    · split
      · rename_i hik hik'
        subst hik'
        rw [show k + 4 - (k + 1 + 2) = 0 + 1 from by omega]
        intro V _ _
        exact forcesOn_one_right (k + 1 + 2)
      · rename_i hik hik'
        rw [show k + 4 - (i + 2) = 0 from by omega]
        intro V _ _
        exact forcesOn_zero_right 0 (i + 2)

-- Validity of the table, antidiagonal by antidiagonal.
theorem rows_forces : ∀ k, (∀ j, ForcesOn ((rows k).1 j) j (k + 3 - j)) ∧
    (∀ j, ForcesOn ((rows k).2 j) j (k + 2 - j)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro j
      match j with
      | 0 =>
        show ForcesOn 0 0 (0 + 3 - 0)
        intro V _ _
        exact forcesOn_zero_left 0 (0 + 3 - 0)
      | 1 =>
        show ForcesOn 1 1 (0 + 3 - 1)
        intro V _ _
        exact forcesOn_one_left (0 + 3 - 1)
      | 2 =>
        show ForcesOn 1 2 (0 + 3 - 2)
        intro V _ _
        exact forcesOn_one_right 2
      | j + 3 =>
        rw [show 0 + 3 - (j + 3) = 0 from by omega]
        intro V _ _
        exact forcesOn_zero_right ((rows 0).1 (j + 3)) (j + 3)
    · intro j
      match j with
      | 0 =>
        show ForcesOn 0 0 (0 + 2 - 0)
        intro V _ _
        exact forcesOn_zero_left 0 (0 + 2 - 0)
      | 1 =>
        show ForcesOn 1 1 (0 + 2 - 1)
        intro V _ _
        exact forcesOn_one_left (0 + 2 - 1)
      | j + 2 =>
        rw [show 0 + 2 - (j + 2) = 0 from by omega]
        intro V _ _
        exact forcesOn_zero_right ((rows 0).2 (j + 2)) (j + 2)
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · intro j
      rw [show k + 1 + 3 - j = k + 4 - j from by omega]
      show ForcesOn (next k (rows k).1 (rows k).2 j) j (k + 4 - j)
      intro V _ _
      exact next_forces k (rows k).1 (rows k).2 ih.1 ih.2 (rows_pos k).1 j
    · intro j
      rw [show k + 1 + 2 - j = k + 3 - j from by omega]
      show ForcesOn ((rows k).1 j) j (k + 3 - j)
      intro V _ _
      exact ih.1 j

-- The table never exceeds V001's.
theorem rows_le : ∀ k, (∀ j, (rows k).1 j ≤ V001.dRow (k + 1) j) ∧
    (∀ j, (rows k).2 j ≤ V001.dRow k j) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro j
      match j with
      | 0 => exact Nat.zero_le _
      | j + 1 =>
        show row1 (j + 1) ≤ V001.dRow (0 + 1) (j + 1)
        rw [row1_succ, V001.dRow_succ, row0_eq, row0_eq]
    · intro j
      show row0 j ≤ V001.dRow 0 j
      rw [row0_eq]
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · intro j
      show next k (rows k).1 (rows k).2 j ≤ V001.dRow (k + 1 + 1) j
      match j with
      | 0 => exact Nat.zero_le _
      | 1 =>
        show 1 ≤ V001.dRow (k + 1 + 1) 1
        exact V001.dRow_pos (k + 1 + 1) 1 (by omega) (by omega)
      | i + 2 =>
        simp only [next]
        split_ifs with hik hik'
        · rw [show V001.dRow (k + 1 + 1) (i + 2)
              = V001.stepVal (V001.dRow (k + 1) (i + 1)) (V001.dRow (k + 1) (i + 2)) from
              V001.dRow_succ (k + 1) (i + 1)]
          refine le_trans (walker_le _ _ _) (stepVal_mono ?_ ?_)
          · exact mir_le ih.1 (rows_zero_left k) (v1_dRow_symm' k) (i + 1)
          · exact mir_le ih.1 (rows_zero_left k) (v1_dRow_symm' k) (i + 2)
        · exact V001.dRow_pos (k + 1 + 1) (i + 2) (by omega) (by omega)
        · exact Nat.zero_le _
    · intro j
      show (rows k).1 j ≤ V001.dRow (k + 1) j
      exact ih.1 j

-- The obligations.
theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey.f record := by
  intro n
  rcases Nat.lt_or_ge n nMin with h | h
  · rw [SqueezeBench.Ramsey.f, if_pos h]
    exact Nat.zero_le _
  · have h2 : 2 ≤ n := by rwa [nMin_eq] at h
    have hf : ForcesOn ((rows (2 * n - 3)).1 n) n (2 * n - 3 + 3 - n) := by
      intro V _ _
      exact (rows_forces _).1 n
    rw [show 2 * n - 3 + 3 - n = n from by omega] at hf
    exact f_le_of_forces h (forces_of_forcesOn hf)

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey.Upper.V001.record record := by
  intro n
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> decide
  · show (rows (2 * n - 3)).1 n ≤ V001.dRow (2 * n - 2) n
    have hle := (rows_le (2 * n - 3)).1 n
    rwa [show 2 * n - 3 + 1 = 2 * n - 2 from by omega] at hle

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Upper.V001.record record :=
  ⟨5, by decide, by decide +kernel⟩

end SqueezeBench.Ramsey.Upper.V002
