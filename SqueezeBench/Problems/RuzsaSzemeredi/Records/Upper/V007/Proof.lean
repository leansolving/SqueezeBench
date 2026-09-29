import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V007.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V006.Proof

/-! Record V007 for RuzsaSzemeredi, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/RuzsaSzemeredi/Upper/V007.lean`. -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V007

open Finset SimpleGraph
open SqueezeBench.RuzsaSzemeredi.Upper.V006 (trianglesAt degree_eq degree_sum_triangle_le'
  filter_neighbor_eq)

-- Exactly one triangle contains a given edge `uv`.
theorem card_filter_mem_eq_one {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) {u v : Fin m} (huv : G.Adj u v) :
    #((trianglesAt G u).filter (fun τ => v ∈ τ)) = 1 := by
  obtain ⟨τ₀, hτ₀, huτ₀, hvτ₀⟩ := hG.2 huv
  rw [Finset.card_eq_one]
  refine ⟨τ₀, ?_⟩
  ext τ
  simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff, mem_singleton]
  constructor
  · rintro ⟨⟨hτ, huτ⟩, hvτ⟩
    by_contra hne
    have hsub := hG.1 (by simpa [mem_cliqueSet_iff] using hτ)
      (by simpa [mem_cliqueSet_iff] using hτ₀) hne
    exact (G.ne_of_adj huv) (hsub ⟨huτ, huτ₀⟩ ⟨hvτ, hvτ₀⟩)
  · rintro rfl
    exact ⟨⟨hτ₀, huτ₀⟩, hvτ₀⟩

-- (A) The triangles through `v`, and for each neighbour `u` the triangles through `u` avoiding
-- `v`, are pairwise disjoint: a triangle avoiding `v` through two neighbours `u, u'` of `v` would
-- share the edge `uu'` with the triangle `{v, u, u'}`. Hence `t_v + Σ_{u ∈ N(v)} (t_u − 1) ≤ T`.
theorem sum_nbr_le {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (v : Fin m) :
    ∑ u ∈ G.neighborFinset v, #(trianglesAt G u) ≤ #(G.cliqueFinset 3) + #(trianglesAt G v) := by
  set B : Fin m → Finset (Finset (Fin m)) := fun u => (trianglesAt G u).filter (fun τ => v ∉ τ)
    with hB
  have hcard : ∀ u ∈ G.neighborFinset v, #(trianglesAt G u) = #(B u) + 1 := by
    intro u hu
    rw [mem_neighborFinset] at hu
    have h := Finset.card_filter_add_card_filter_not (s := trianglesAt G u)
      (fun τ => v ∈ τ)
    rw [card_filter_mem_eq_one hG hu.symm] at h
    simp only [hB]
    omega
  have hdisj : (↑(G.neighborFinset v) : Set (Fin m)).PairwiseDisjoint B := by
    intro u hu u' hu' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro τ hτ hτ'
    simp only [hB, trianglesAt, mem_filter, mem_cliqueFinset_iff] at hτ hτ'
    have hu : G.Adj v u := by simpa using hu
    have hu' : G.Adj v u' := by simpa using hu'
    have huu' : G.Adj u u' := hτ.1.1.1 hτ.1.2 hτ'.1.2 hne
    have hclique : G.IsNClique 3 {v, u, u'} := is3Clique_triple_iff.mpr ⟨hu, hu', huu'⟩
    have hneq : ({v, u, u'} : Finset (Fin m)) ≠ τ := by
      intro h
      exact hτ.2 (h ▸ by simp)
    have hsub := hG.1 (by simpa [mem_cliqueSet_iff] using hclique)
      (by simpa [mem_cliqueSet_iff] using hτ.1.1) hneq
    exact hne (hsub ⟨by simp, hτ.1.2⟩ ⟨by simp, hτ'.1.2⟩)
  have hdisj2 : Disjoint (trianglesAt G v) ((G.neighborFinset v).biUnion B) := by
    rw [Finset.disjoint_left]
    intro τ hτ hτ'
    simp only [trianglesAt, mem_filter] at hτ
    simp only [mem_biUnion, hB, trianglesAt, mem_filter] at hτ'
    obtain ⟨u, -, -, hvτ⟩ := hτ'
    exact hvτ hτ.2
  have hsub : trianglesAt G v ∪ (G.neighborFinset v).biUnion B ⊆ G.cliqueFinset 3 := by
    intro τ hτ
    simp only [mem_union, mem_biUnion, hB, trianglesAt, mem_filter] at hτ
    rcases hτ with h | ⟨u, -, h, -⟩
    · exact h.1
    · exact h.1
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_biUnion hdisj] at h1
  calc ∑ u ∈ G.neighborFinset v, #(trianglesAt G u)
      = ∑ u ∈ G.neighborFinset v, (#(B u) + 1) := Finset.sum_congr rfl hcard
    _ = ∑ u ∈ G.neighborFinset v, #(B u) + #(G.neighborFinset v) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ u ∈ G.neighborFinset v, #(B u) + 2 * #(trianglesAt G v) := by
        rw [← degree_eq G hG v]; rfl
    _ ≤ #(G.cliqueFinset 3) + #(trianglesAt G v) := by omega

-- The neighbourhood of `v` is the disjoint union, over the triangles at `v`, of their two other
-- vertices.
theorem neighborFinset_eq_biUnion {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (v : Fin m) :
    G.neighborFinset v = (trianglesAt G v).biUnion (fun τ => τ.erase v) := by
  ext u
  simp only [mem_neighborFinset, mem_biUnion, trianglesAt, mem_filter, mem_cliqueFinset_iff,
    mem_erase]
  constructor
  · intro huv
    obtain ⟨τ, hτ, hvτ, huτ⟩ := hG.2 huv
    exact ⟨τ, ⟨hτ, hvτ⟩, (G.ne_of_adj huv).symm, huτ⟩
  · rintro ⟨τ, ⟨hτ, hvτ⟩, hne, huτ⟩
    exact hτ.1 hvτ huτ (Ne.symm hne)

theorem pairwiseDisjoint_erase {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (v : Fin m) :
    (↑(trianglesAt G v) : Set (Finset (Fin m))).PairwiseDisjoint (fun τ => τ.erase v) := by
  intro τ hτ τ' hτ' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro u hu hu'
  simp only [Finset.mem_coe, trianglesAt, mem_filter, mem_cliqueFinset_iff] at hτ hτ'
  simp only [mem_erase] at hu hu'
  have hsub := hG.1 (by simpa [mem_cliqueSet_iff] using hτ.1)
    (by simpa [mem_cliqueSet_iff] using hτ'.1) hne
  exact hu.1 (hsub ⟨hu.2, hu'.2⟩ ⟨hτ.2, hτ'.2⟩)

-- (B) Along each triangle at `v` the three triangle counts add up to at most `(m + c)/2`, so the
-- `t_v` triangles at `v` give `2 Σ_{u ∈ N(v)} t_u + 2 t_v² ≤ t_v (m + c)`.
theorem two_mul_sum_nbr_le {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (v : Fin m) :
    2 * ∑ u ∈ G.neighborFinset v, #(trianglesAt G u) + 2 * #(trianglesAt G v) * #(trianglesAt G v)
      ≤ #(trianglesAt G v) * (m + 2 + m % 2) := by
  rw [neighborFinset_eq_biUnion hG v, Finset.sum_biUnion (pairwiseDisjoint_erase hG v)]
  have key : ∀ τ ∈ trianglesAt G v,
      2 * ∑ u ∈ τ.erase v, #(trianglesAt G u) + 2 * #(trianglesAt G v) ≤ m + 2 + m % 2 := by
    intro τ hτ
    simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff] at hτ
    have h1 := degree_sum_triangle_le' hG hτ.1
    have h2 : ∑ u ∈ τ, G.degree u = 2 * ∑ u ∈ τ, #(trianglesAt G u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun u _ => degree_eq G hG u)
    have h3 := Finset.sum_erase_add τ (fun u => #(trianglesAt G u)) hτ.2
    omega
  have := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at this
  nlinarith [this]

-- Double counting `Σ_v Σ_{u ∈ N(v)} t_u = Σ_u deg u · t_u = 2 Σ_u t_u²`.
theorem sum_sum_nbr_eq {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) :
    ∑ v : Fin m, ∑ u ∈ G.neighborFinset v, #(trianglesAt G u)
      = 2 * ∑ v : Fin m, #(trianglesAt G v) ^ 2 := by
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset (Fin m)))
    (s' := fun u => G.neighborFinset u) (f := fun (_ : Fin m) (u : Fin m) => #(trianglesAt G u))
    (fun v u => by simp [adj_comm])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_const, smul_eq_mul, show #(G.neighborFinset u) = G.degree u from rfl,
    degree_eq G hG u]
  ring


-- A convex function on `ℕ` lies above its chord through `q` and `q + 1`, extended as a line.
theorem tangent_of_convex (g : ℕ → ℤ) (hconv : ∀ t, 2 * g (t + 1) ≤ g t + g (t + 2)) (q : ℕ) :
    ∀ t : ℕ, g q + (g (q + 1) - g q) * ((t : ℤ) - q) ≤ g t := by
  have hmono : Monotone (fun t => g (t + 1) - g t) := by
    refine monotone_nat_of_le_succ (fun t => ?_)
    have := hconv t
    show g (t + 1) - g t ≤ g (t + 1 + 1) - g (t + 1)
    rw [show t + 1 + 1 = t + 2 by omega]
    omega
  have hup : ∀ k : ℕ, g q + (g (q + 1) - g q) * k ≤ g (q + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hmono (Nat.le_add_right q k)
      simp only at this
      push_cast
      rw [show q + (k + 1) = q + k + 1 by ring]
      nlinarith [this, ih]
  have hdown : ∀ k t : ℕ, t + k = q → g q - (g (q + 1) - g q) * k ≤ g t := by
    intro k
    induction k with
    | zero => intro t h; subst h; simp
    | succ k ih =>
      intro t h
      have h' : (t + 1) + k = q := by omega
      have := ih (t + 1) h'
      have hm := hmono (show t ≤ q by omega)
      simp only at hm
      push_cast
      nlinarith [this, hm]
  intro t
  rcases le_or_gt q t with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have := hup k
    push_cast at this ⊢
    nlinarith [this]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
    have := hdown (k + 1) t (by omega)
    have hq : (q : ℤ) = t + k + 1 := by rw [hk]; push_cast; ring
    rw [hq]
    push_cast at this ⊢
    nlinarith [this]

-- Hence, over any family with sum `S = q·n + r`, the balanced values `q` and `q + 1` minimise.
theorem balanced_le_sum {n : ℕ} (g : ℕ → ℤ) (hconv : ∀ t, 2 * g (t + 1) ≤ g t + g (t + 2))
    (t : Fin n → ℕ) (q r : ℕ) (hS : ∑ v, t v = q * n + r) :
    ((n : ℤ) - r) * g q + r * g (q + 1) ≤ ∑ v, g (t v) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun v _ => tangent_of_convex g hconv q (t v))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin] at h
  have hS' : (∑ v, (t v : ℤ)) = q * n + r := by exact_mod_cast hS
  rw [hS'] at h
  simp only [nsmul_eq_mul] at h
  nlinarith [h]

-- The convex function: `4t² − 2·min(T + t, t(n+c)/2 − t²)`, i.e. the maximum of two convex
-- quadratics.
theorem convex_g (a b : ℤ) :
    ∀ t : ℕ, 2 * max (4 * ((t + 1 : ℕ) : ℤ) ^ 2 - 2 * a - 2 * (t + 1 : ℕ))
        (6 * ((t + 1 : ℕ) : ℤ) ^ 2 - b * (t + 1 : ℕ))
      ≤ max (4 * (t : ℤ) ^ 2 - 2 * a - 2 * t) (6 * (t : ℤ) ^ 2 - b * t)
        + max (4 * ((t + 2 : ℕ) : ℤ) ^ 2 - 2 * a - 2 * (t + 2 : ℕ))
          (6 * ((t + 2 : ℕ) : ℤ) ^ 2 - b * (t + 2 : ℕ)) := by
  intro t
  push_cast
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℤ) ≤ 2)]
  apply max_le
  · have h1 := le_max_left (4 * (t : ℤ) ^ 2 - 2 * a - 2 * t) (6 * (t : ℤ) ^ 2 - b * t)
    have h2 := le_max_left (4 * ((t : ℤ) + 2) ^ 2 - 2 * a - 2 * ((t : ℤ) + 2))
      (6 * ((t : ℤ) + 2) ^ 2 - b * ((t : ℤ) + 2))
    nlinarith [h1, h2]
  · have h1 := le_max_right (4 * (t : ℤ) ^ 2 - 2 * a - 2 * t) (6 * (t : ℤ) ^ 2 - b * t)
    have h2 := le_max_right (4 * ((t : ℤ) + 2) ^ 2 - 2 * a - 2 * ((t : ℤ) + 2))
      (6 * ((t : ℤ) + 2) ^ 2 - b * ((t : ℤ) + 2))
    nlinarith [h1, h2]

-- `4t² − cap t` is at most the convex function, whatever the truncated subtraction does.
theorem sq_sub_cap_le (n T t : ℕ) :
    4 * (t : ℤ) ^ 2 - (cap n T t : ℤ)
      ≤ max (4 * (t : ℤ) ^ 2 - 2 * T - 2 * t) (6 * (t : ℤ) ^ 2 - ((n + 2 + n % 2 : ℕ) : ℤ) * t) := by
  unfold cap
  rcases le_or_gt (2 * T + 2 * t) (t * (n + 2 + n % 2) - 2 * t * t) with h | h
  · rw [min_eq_left h]
    refine le_trans ?_ (le_max_left _ _)
    push_cast
    linarith
  · rw [min_eq_right h.le]
    refine le_trans ?_ (le_max_right _ _)
    have : ((t * (n + 2 + n % 2) - 2 * t * t : ℕ) : ℤ)
        ≥ (t : ℤ) * ((n + 2 + n % 2 : ℕ) : ℤ) - 2 * t * t := by
      rcases le_or_gt (2 * t * t) (t * (n + 2 + n % 2)) with h1 | h1
      · rw [Nat.cast_sub h1]; push_cast; linarith
      · rw [Nat.sub_eq_zero_of_le h1.le]
        have h2 : ((t * (n + 2 + n % 2) : ℕ) : ℤ) < ((2 * t * t : ℕ) : ℤ) := by exact_mod_cast h1
        push_cast at h2 ⊢
        linarith
    push_cast at this ⊢
    nlinarith [this]

-- The triangle counts of a locally linear graph pass the test.
theorem ok_of_counts {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : ok n #(G.cliqueFinset 3) = true := by
  set T := #(G.cliqueFinset 3) with hT
  set t : Fin n → ℕ := fun v => #(trianglesAt G v) with ht
  set q := 3 * T / n with hq
  set r := 3 * T % n with hr
  have hS : ∑ v, t v = q * n + r := by
    have h1 : ∑ v, t v = 3 * T := SqueezeBench.RuzsaSzemeredi.Upper.V006.sum_card_trianglesAt G
    have h2 := Nat.div_add_mod (3 * T) n
    rw [h1, ← h2]; ring
  have hrn : r < n := Nat.mod_lt _ hn
  -- the per-vertex bounds, in `ℤ`
  set g : ℕ → ℤ := fun s => max (4 * (s : ℤ) ^ 2 - 2 * T - 2 * s)
    (6 * (s : ℤ) ^ 2 - ((n + 2 + n % 2 : ℕ) : ℤ) * s) with hg
  have hconv : ∀ s, 2 * g (s + 1) ≤ g s + g (s + 2) := convex_g (T : ℤ) ((n + 2 + n % 2 : ℕ) : ℤ)
  have hvert : ∀ v, g (t v) ≤ 4 * (t v : ℤ) ^ 2 - 2 * ∑ u ∈ G.neighborFinset v, (t u : ℤ) := by
    intro v
    have hA := sum_nbr_le hG v
    have hB := two_mul_sum_nbr_le hG v
    have hA' : ((∑ u ∈ G.neighborFinset v, #(trianglesAt G u) : ℕ) : ℤ) ≤ T + t v := by
      exact_mod_cast hA
    have hB' : 2 * ((∑ u ∈ G.neighborFinset v, #(trianglesAt G u) : ℕ) : ℤ)
        + 2 * (t v : ℤ) * t v ≤ (t v : ℤ) * ((n + 2 + n % 2 : ℕ) : ℤ) := by
      exact_mod_cast hB
    have hcast : ((∑ u ∈ G.neighborFinset v, #(trianglesAt G u) : ℕ) : ℤ)
        = ∑ u ∈ G.neighborFinset v, (t u : ℤ) := by push_cast; rfl
    rw [hcast] at hA' hB'
    simp only [hg]
    apply max_le
    · nlinarith [hA']
    · nlinarith [hB']
  have hsum : ∑ v, g (t v) ≤ 0 := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hvert v)
    have h2 : ∑ v, (4 * (t v : ℤ) ^ 2 - 2 * ∑ u ∈ G.neighborFinset v, (t u : ℤ)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have := sum_sum_nbr_eq hG
      have hc : ((∑ v : Fin n, ∑ u ∈ G.neighborFinset v, #(trianglesAt G u) : ℕ) : ℤ)
          = ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, (t u : ℤ) := by push_cast; rfl
      have hc2 : ((2 * ∑ v : Fin n, #(trianglesAt G v) ^ 2 : ℕ) : ℤ)
          = 2 * ∑ v : Fin n, (t v : ℤ) ^ 2 := by push_cast; rfl
      have h3 : ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, (t u : ℤ) = 2 * ∑ v : Fin n, (t v : ℤ) ^ 2 := by
        rw [← hc, ← hc2, this]
      rw [h3]; ring
    linarith [h1, h2]
  have hbal := balanced_le_sum g hconv t q r hS
  -- translate to the `ℕ` test
  have hcapq := sq_sub_cap_le n T q
  have hcapq1 := sq_sub_cap_le n T (q + 1)
  have hgq : g q = max (4 * (q : ℤ) ^ 2 - 2 * T - 2 * q)
    (6 * (q : ℤ) ^ 2 - ((n + 2 + n % 2 : ℕ) : ℤ) * q) := rfl
  have hgq1 : g (q + 1) = max (4 * ((q + 1 : ℕ) : ℤ) ^ 2 - 2 * T - 2 * (q + 1 : ℕ))
    (6 * ((q + 1 : ℕ) : ℤ) ^ 2 - ((n + 2 + n % 2 : ℕ) : ℤ) * (q + 1 : ℕ)) := rfl
  rw [← hgq] at hcapq
  rw [← hgq1] at hcapq1
  have hfinal : ((n : ℤ) - r) * (4 * (q : ℤ) ^ 2 - (cap n T q : ℤ))
      + r * (4 * ((q + 1 : ℕ) : ℤ) ^ 2 - (cap n T (q + 1) : ℤ)) ≤ 0 := by
    have hnr : (0 : ℤ) ≤ (n : ℤ) - r := by omega
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcapq hnr, mul_le_mul_of_nonneg_left hcapq1 hr0,
      hbal, hsum]
  unfold ok
  simp only [decide_eq_true_iff]
  rw [← hq, ← hr]
  have hnr' : ((n - r : ℕ) : ℤ) = (n : ℤ) - r := by omega
  have key : ((n - r : ℕ) : ℤ) * (4 * q * q) + (r : ℤ) * (4 * (q + 1) * (q + 1))
      ≤ ((n - r : ℕ) : ℤ) * (cap n T q : ℤ) + (r : ℤ) * (cap n T (q + 1) : ℤ) := by
    rw [hnr']
    push_cast at hfinal
    nlinarith [hfinal]
  exact_mod_cast key

-- The search returns at most its starting point, and at least any passing value below it.
theorem search_le (n : ℕ) : ∀ T, search n T ≤ T := by
  intro T
  induction T with
  | zero => simp [search]
  | succ T ih =>
    simp only [search]
    cases ok n (T + 1)
    · simp; omega
    · simp

theorem le_search (n : ℕ) {T : ℕ} (hT : ok n T = true) : ∀ T₀, T ≤ T₀ → T ≤ search n T₀ := by
  intro T₀
  induction T₀ with
  | zero => intro h; omega
  | succ T₀ ih =>
    intro h
    simp only [search]
    rcases Nat.lt_or_ge T (T₀ + 1) with hlt | hge
    · have := ih (by omega)
      cases hok : ok n (T₀ + 1)
      · simpa using this
      · simp; omega
    · have hEq : T = T₀ + 1 := by omega
      subst hEq
      rw [hT]; rfl

theorem ok_ruzsaSzemeredi {n : ℕ} (hn : 0 < n) : ok n (ruzsaSzemerediNumberNat n) = true := by
  obtain ⟨G, inst, hcard, hLL⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  rw [show ruzsaSzemerediNumberNat n = ruzsaSzemerediNumber (Fin n) from rfl, ← hcard]
  exact ok_of_counts hn hLL

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := by
  intro n
  rcases lt_or_ge n SqueezeBench.RuzsaSzemeredi.nMin with h | h
  · have h' : n < 3 := h
    simp [SqueezeBench.RuzsaSzemeredi.f, h']
  · have hprev := SqueezeBench.RuzsaSzemeredi.Upper.V006.valid n
    rw [SqueezeBench.RuzsaSzemeredi.f_of_le h] at hprev ⊢
    have h' : 3 ≤ n := h
    exact le_search n (ok_ruzsaSzemeredi (by omega)) _ hprev

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V006.record record :=
  fun n => search_le n _

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V006.record record :=
  ⟨13, by decide, by decide⟩

end SqueezeBench.RuzsaSzemeredi.Upper.V007
