import SqueezeBench.Problems.Ramsey3.Records.Upper.V004.Def
import SqueezeBench.Problems.Ramsey3.Records.Upper.V003.Proof

/-! Record V004 for Ramsey3, upper direction, by trial claude-fable: the three obligations.

The mathematics is a second level of the deletion argument of V003, applied inside `G - N[v]`
for the vertex `v` whose neighbours have the largest degree sum, in Jensen form (Cauchy–Schwarz
on the degrees of `G - N[v]` instead of the per-vertex minimisation), so that the resulting
bound `α ≥ 1 + q(m, X/m)` with `m = n - 1 - D`, `X = D (n - 2D)`,
`q(m, x) = 1 + a (m - 1 - x) - β x (m - 2x)` depends only on `n` and `D`. The record checks
that `1 + q(m, X/m) > D` at a candidate `N₀` (in ℕ, after clearing denominators), and the
proof restricts any larger graph to an induced subgraph on exactly `N₀` vertices, so no
monotonicity in `n` is needed. The graph lemmas of V002 and V003 carry the whole argument. -/

namespace SqueezeBench.Ramsey3.Upper.V004

open Finset SimpleGraph SqueezeBench SqueezeBench.Ramsey SqueezeBench.Ramsey3.Upper.V002
  SqueezeBench.Ramsey3.Upper.V003

/-- Monotonicity of `q(m, x) = 1 + a (m - 1 - x) - β x (m - 2x)`: decreasing in `x` and
increasing in `m` on the relevant ranges. -/
theorem q_mono {a β m m' x x₀ : ℚ} (hβ : 0 ≤ β) (ha : β * x₀ ≤ a) (hmm : m ≤ m')
    (hx : x ≤ x₀) (hx0 : 0 ≤ x) (h4 : 4 * x₀ ≤ m) :
    1 + a * (m - 1 - x₀) - β * x₀ * (m - 2 * x₀)
      ≤ 1 + a * (m' - 1 - x) - β * x * (m' - 2 * x) := by
  have e1 : 0 ≤ (x₀ - x) * (a + β * m' - 2 * β * (x + x₀)) := by
    apply mul_nonneg (by linarith)
    have h1 : 0 ≤ β * (m' - 2 * (x + x₀)) := mul_nonneg hβ (by linarith)
    have h2 : 0 ≤ β * x₀ := mul_nonneg hβ (le_trans hx0 hx)
    linarith
  have e2 : 0 ≤ (m' - m) * (a - β * x₀) := mul_nonneg (by linarith) (by linarith)
  linarith [e1, e2]

/-- The arithmetic of the certificate: `q(m, X/m) ≤ D - 1` contradicts `check`. -/
theorem check_arith (D m X A B q' : ℕ) (hD : 2 ≤ D) (hm : 1 ≤ m) (hq' : 0 < q')
    (hineq : (D - 2) * q' * m * m + B * X * m * m + A * m * X
      < A * m * (m * (m - 1)) + 2 * B * X * X)
    (hq : 1 + ((A : ℚ) / q') * ((m : ℚ) - 1 - (X : ℚ) / m)
        - ((B : ℚ) / q') * ((X : ℚ) / m) * ((m : ℚ) - 2 * ((X : ℚ) / m)) ≤ (D : ℚ) - 1) :
    False := by
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hq'q : (0 : ℚ) < q' := by exact_mod_cast hq'
  have hD2 : ((D - 2 : ℕ) : ℚ) = (D : ℚ) - 2 := by rw [Nat.cast_sub hD]; push_cast; ring
  have hm1 : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by rw [Nat.cast_sub hm]; push_cast; ring
  have hineqQ : ((D - 2 : ℕ) : ℚ) * q' * m * m + B * X * m * m + A * m * X
      < A * m * (m * ((m - 1 : ℕ) : ℚ)) + 2 * B * X * X := by exact_mod_cast hineq
  rw [hD2, hm1] at hineqQ
  have key : (q' : ℚ) * m * m * (1 + ((A : ℚ) / q') * ((m : ℚ) - 1 - (X : ℚ) / m)
        - ((B : ℚ) / q') * ((X : ℚ) / m) * ((m : ℚ) - 2 * ((X : ℚ) / m)))
      = q' * m * m + A * m * m * (m - 1) - A * m * X - B * X * m * m + 2 * B * X * X := by
    field_simp
    ring
  have h2 := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℚ) ≤ q' * m * m)
  rw [key] at h2
  linarith

/-- `a = sh r + r · del (r+1)` over the common denominator `q(r+1)`. -/
theorem a_eq (r : ℕ) : sh r + r * del (r + 1) = (((shearer r).1 * ((r + 1) * (r + 1) + 1)
      + r * ((shearer r).1 * ((r + 1) * (r + 1) + 1) - (shearer (r + 1)).1) : ℕ) : ℚ)
      / (shearer (r + 1)).2 := by
  rw [del_succ_eq r, sh_eq_over r]
  push_cast
  ring

/-- `σ = p₁ - 2s ≤ D (n - 2D)` when `p₁ ≤ nD`, `p₁² ≤ n² s` and `n ≥ 4D`. -/
theorem sigma_le (n D p1 s : ℚ) (hn : 4 * D ≤ n) (hn0 : 0 < n) (hp1 : p1 ≤ n * D)
    (hs : p1 ^ 2 ≤ n * (n * s)) : p1 - 2 * s ≤ D * (n - 2 * D) := by
  have hkey : 0 ≤ (n * D - p1) * (n * n - 2 * n * D - 2 * p1) := by
    apply mul_nonneg (by linarith)
    have : 2 * p1 ≤ 2 * (n * D) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hn hn0.le]
  have h1 : n * n * (p1 - 2 * s) ≤ n * n * (D * (n - 2 * D)) := by
    nlinarith [hs, hkey]
  exact le_of_mul_le_mul_left h1 (by positivity)

/-- `x₀ = D (n - 2D) / (n - 1 - D)` lies in `[0, D]`. -/
theorem x0_le (n D : ℚ) (hD : 1 ≤ D) (hn : 5 * D + 1 ≤ n) :
    0 ≤ D * (n - 2 * D) / (n - 1 - D) ∧ D * (n - 2 * D) / (n - 1 - D) ≤ D := by
  have hm : 0 < n - 1 - D := by linarith
  constructor
  · apply div_nonneg _ hm.le
    apply mul_nonneg (by linarith)
    linarith
  · rw [div_le_iff₀ hm]
    nlinarith [hD]

/-- The slope condition of the certificate, in ℚ. -/
theorem slope_pos (r D : ℕ)
    (hslope : ((shearer r).1 * ((r + 1) * (r + 1) + 1) - (shearer (r + 1)).1) * D
      < (shearer r).1 * ((r + 1) * (r + 1) + 1)
        + r * ((shearer r).1 * ((r + 1) * (r + 1) + 1) - (shearer (r + 1)).1)) :
    del (r + 1) * D < sh r + r * del (r + 1) := by
  have hq' : (0 : ℚ) < (shearer (r + 1)).2 := by exact_mod_cast (shearer_pos (r + 1)).2
  rw [a_eq r, del_succ_eq r, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hq']
  exact_mod_cast hslope

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem com_comm (S : Finset V) (u v : V) : com G S u v = com G S v u := by
  ext w; simp only [com, mem_filter]; tauto

/-- The V003 identity: the sum over `v ∈ S` of the local deletion bounds. -/
theorem sum_local (htf : G.CliqueFree 3) (S : Finset V) (r : ℕ) :
    ∑ v ∈ S, (1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ)))
      = ∑ u ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S u).card)
        - del (r + 1) * (((nbr G S u).card : ℚ) * ((S.card : ℚ) - 2 * (nbr G S u).card))) := by
  have hA : ∀ v ∈ S, ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ))
      = (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S v).card)
        - del (r + 1) * ∑ u ∈ non G S v, ((nbr G (non G S v) u).card : ℚ) := by
    intro v hv
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, card_non G hv]
    ring
  have hL : ∑ v ∈ S, (1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ)))
      = ∑ v ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S v).card))
        - del (r + 1) * ∑ v ∈ S, ∑ u ∈ non G S v, ((nbr G (non G S v) u).card : ℚ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hA v hv]
    ring
  rw [hL, sum_deg_non G htf S, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The deletion bound inside `S` in Jensen form: an independent set of size at least
`q(m, σ/m)` with `m = |S|` and `σ` the degree sum within `S`. -/
theorem avg_bound (htf : G.CliqueFree 3) {S : Finset V} (hS : S.Nonempty) (r : ℕ) :
    ∃ T ⊆ S, G.IsIndepSet (T : Set V) ∧
      1 + (sh r + r * del (r + 1))
          * ((S.card : ℚ) - 1 - (∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)
        - del (r + 1) * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)
          * ((S.card : ℚ) - 2 * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)) ≤ (T.card : ℚ) := by
  have hβ : 0 ≤ del (r + 1) := del_nonneg _
  have local_bound : ∀ v ∈ S, ∃ T ⊆ S, G.IsIndepSet (T : Set V) ∧
      1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ)) ≤ (T.card : ℚ) := by
    intro v hv
    obtain ⟨T', hT'W, hT'ind, hT'card⟩ := shearer_indep G htf (non G S v)
    obtain ⟨h1, h2, h3⟩ := insert_indep G hv hT'W hT'ind
    refine ⟨insert v T', h1, h2, ?_⟩
    rw [h3]
    push_cast
    have h4 : ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ))
        ≤ ∑ u ∈ non G S v, sh (nbr G (non G S v) u).card := by
      refine Finset.sum_le_sum (fun u _ => ?_)
      have := secant r (nbr G (non G S v) u).card
      linarith
    linarith
  have hm : (0 : ℚ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hcs : (∑ u ∈ S, ((nbr G S u).card : ℚ)) ^ 2
      ≤ S.card * ∑ u ∈ S, ((nbr G S u).card : ℚ) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsum : ∑ v ∈ S, (1 + (sh r + r * del (r + 1))
          * ((S.card : ℚ) - 1 - (∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)
        - del (r + 1) * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)
          * ((S.card : ℚ) - 2 * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)))
      ≤ ∑ v ∈ S, (1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ))) := by
    rw [sum_local G htf S r, Finset.sum_const, nsmul_eq_mul]
    have expand : ∑ u ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S u).card)
        - del (r + 1) * (((nbr G S u).card : ℚ) * ((S.card : ℚ) - 2 * (nbr G S u).card)))
        = ∑ u ∈ S, ((1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1))
          - ((sh r + r * del (r + 1)) + del (r + 1) * S.card) * ((nbr G S u).card : ℚ)
          + 2 * del (r + 1) * ((nbr G S u).card : ℚ) ^ 2) :=
      Finset.sum_congr rfl (fun u _ => by ring)
    rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hdiv : (∑ u ∈ S, ((nbr G S u).card : ℚ)) ^ 2 / S.card
        ≤ ∑ u ∈ S, ((nbr G S u).card : ℚ) ^ 2 := by
      rw [div_le_iff₀ hm]; linarith
    have key : (S.card : ℚ) * (1 + (sh r + r * del (r + 1))
          * ((S.card : ℚ) - 1 - (∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)
        - del (r + 1) * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)
          * ((S.card : ℚ) - 2 * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) / S.card)))
        = S.card * (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1))
          - ((sh r + r * del (r + 1)) + del (r + 1) * S.card) * ∑ u ∈ S, ((nbr G S u).card : ℚ)
          + 2 * del (r + 1) * ((∑ u ∈ S, ((nbr G S u).card : ℚ)) ^ 2 / S.card) := by
      field_simp
      ring
    rw [key]
    have := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℚ) ≤ 2 * del (r + 1))
    linarith
  obtain ⟨v, hv, hvle⟩ := Finset.exists_le_of_sum_le hS hsum
  obtain ⟨T, hT, hind, hLv⟩ := local_bound v hv
  exact ⟨T, hT, hind, le_trans hvle hLv⟩

/-- The degree sum of `G[S ∖ N[v]]`: the degree sum of `S` minus twice `Σ_{w ∈ N(v)} deg w`. -/
theorem sum_deg_non_vertex (htf : G.CliqueFree 3) {S : Finset V} {v : V} (hv : v ∈ S) :
    ∑ y ∈ non G S v, ((nbr G (non G S v) y).card : ℚ)
      = ∑ u ∈ S, ((nbr G S u).card : ℚ) - 2 * ∑ w ∈ nbr G S v, ((nbr G S w).card : ℚ) := by
  have h1 : ∑ y ∈ non G S v, ((nbr G (non G S v) y).card : ℚ)
      = ∑ y ∈ non G S v, (((nbr G S y).card : ℚ) - (com G S v y).card) := by
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h : ((nbr G (non G S v) y).card : ℚ) + (com G S y v).card = (nbr G S y).card := by
      exact_mod_cast card_nbr_non G hy
    rw [com_comm G S v y]
    linarith
  have h2 := sum_split G hv (fun u => ((nbr G S u).card : ℚ))
  have h3 : (∑ y ∈ non G S v, ((com G S v y).card : ℚ)) + ((nbr G S v).card : ℚ)
      = ∑ w ∈ nbr G S v, ((nbr G S w).card : ℚ) := by exact_mod_cast count_walks G htf hv
  rw [h1, Finset.sum_sub_distrib]
  linarith

/-- The graph part, with no certificate in sight: a triangle-free graph on at least
`N₀ ≥ 5D + 1` vertices with no independent `(D+1)`-set satisfies `q(m, X/m) ≤ D - 1`. -/
theorem q_le_of_ramsey {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D r N₀ : ℕ) (hD : 2 ≤ D) (hN : 5 * D + 1 ≤ N₀)
    (hsl : del (r + 1) * D < sh r + r * del (r + 1)) (hcard : N₀ ≤ Fintype.card V)
    (htf : G.CliqueFree 3) (hind : ∀ T : Finset V, G.IsIndepSet (T : Set V) → T.card ≤ D) :
    1 + (sh r + r * del (r + 1))
        * (((N₀ : ℚ) - 1 - D) - 1 - (D : ℚ) * (N₀ - 2 * D) / ((N₀ : ℚ) - 1 - D))
      - del (r + 1) * ((D : ℚ) * (N₀ - 2 * D) / ((N₀ : ℚ) - 1 - D))
        * (((N₀ : ℚ) - 1 - D) - 2 * ((D : ℚ) * (N₀ - 2 * D) / ((N₀ : ℚ) - 1 - D)))
      ≤ (D : ℚ) - 1 := by
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (show N₀ ≤ (univ : Finset V).card by rw [Finset.card_univ]; exact hcard)
  have hdeg : ∀ u ∈ S, (nbr G S u).card ≤ D := by
    intro u _
    apply hind
    intro a ha b hb _ hadj
    rw [Finset.mem_coe, mem_nbr] at ha hb
    exact no_triangle G htf ha.2 hadj hb.2
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  -- the vertex whose neighbours have the largest degree sum
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image S
    (fun u => ∑ w ∈ nbr G S u, ((nbr G S w).card : ℚ)) hSne
  have hn : (S.card : ℚ) = N₀ := by exact_mod_cast hScard
  have hdv : ((nbr G S v).card : ℚ) ≤ D := by exact_mod_cast hdeg v hv
  have hcardnon := card_non G hv
  have hDq : (2 : ℚ) ≤ D := by exact_mod_cast hD
  have hNq : 5 * (D : ℚ) + 1 ≤ N₀ := by exact_mod_cast hN
  have hS'ne : (non G S v).Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℚ) < (non G S v).card := by rw [hcardnon, hn]; linarith
    exact_mod_cast this
  obtain ⟨T', hT'W, hT'ind, hT'bound⟩ := avg_bound G htf hS'ne r
  obtain ⟨h1, h2, h3⟩ := insert_indep G hv hT'W hT'ind
  have hTD : ((insert v T').card : ℚ) ≤ D := by exact_mod_cast hind _ h2
  rw [h3] at hTD
  push_cast at hTD
  -- degree statistics
  have hσ := sum_deg_non_vertex G htf hv
  have hp1 : ∑ u ∈ S, ((nbr G S u).card : ℚ) ≤ N₀ * D := by
    have := Finset.sum_le_sum (fun u hu => (show ((nbr G S u).card : ℚ) ≤ D by
      exact_mod_cast hdeg u hu))
    rw [Finset.sum_const, nsmul_eq_mul, hn] at this
    exact this
  have hsv : (∑ u ∈ S, ((nbr G S u).card : ℚ)) ^ 2
      ≤ (N₀ : ℚ) * (N₀ * ∑ w ∈ nbr G S v, ((nbr G S w).card : ℚ)) := by
    have hcs : (∑ u ∈ S, ((nbr G S u).card : ℚ)) ^ 2
        ≤ S.card * ∑ u ∈ S, ((nbr G S u).card : ℚ) ^ 2 := sq_sum_le_card_mul_sum_sq
    have hsum_s : ∑ u ∈ S, ∑ w ∈ nbr G S u, ((nbr G S w).card : ℚ)
        = ∑ u ∈ S, ((nbr G S u).card : ℚ) ^ 2 := by
      rw [sum_nbr G S (fun w => ((nbr G S w).card : ℚ))]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      ring
    have hle : ∑ u ∈ S, ∑ w ∈ nbr G S u, ((nbr G S w).card : ℚ)
        ≤ ∑ u ∈ S, ∑ w ∈ nbr G S v, ((nbr G S w).card : ℚ) :=
      Finset.sum_le_sum (fun u hu => hmax u hu)
    rw [Finset.sum_const, nsmul_eq_mul, hn, hsum_s] at hle
    rw [hn] at hcs
    have hN0 : (0 : ℚ) ≤ N₀ := by positivity
    exact le_trans hcs (mul_le_mul_of_nonneg_left hle hN0)
  have hσ0 : 0 ≤ ∑ y ∈ non G S v, ((nbr G (non G S v) y).card : ℚ) :=
    Finset.sum_nonneg (fun u _ => by positivity)
  have hσX : ∑ y ∈ non G S v, ((nbr G (non G S v) y).card : ℚ) ≤ (D : ℚ) * (N₀ - 2 * D) := by
    rw [hσ]
    exact sigma_le N₀ D _ _ (by linarith) (by linarith) hp1 hsv
  have hm'pos : (0 : ℚ) < (non G S v).card := by rw [hcardnon, hn]; linarith
  have hmpos : (0 : ℚ) < (N₀ : ℚ) - 1 - D := by linarith
  obtain ⟨hx0, hx0D⟩ := x0_le N₀ D (by linarith) hNq
  have hβ : 0 ≤ del (r + 1) := del_nonneg _
  have hchain := q_mono (a := sh r + r * del (r + 1)) (β := del (r + 1))
    (m := (N₀ : ℚ) - 1 - D) (m' := ((non G S v).card : ℚ))
    (x := (∑ y ∈ non G S v, ((nbr G (non G S v) y).card : ℚ)) / (non G S v).card)
    (x₀ := (D : ℚ) * (N₀ - 2 * D) / ((N₀ : ℚ) - 1 - D))
    hβ (le_trans (mul_le_mul_of_nonneg_left hx0D hβ) hsl.le)
    (by rw [hcardnon, hn]; linarith)
    (calc (∑ y ∈ non G S v, ((nbr G (non G S v) y).card : ℚ)) / (non G S v).card
          ≤ (D : ℚ) * (N₀ - 2 * D) / (non G S v).card :=
            div_le_div_of_nonneg_right hσX hm'pos.le
        _ ≤ (D : ℚ) * (N₀ - 2 * D) / ((N₀ : ℚ) - 1 - D) := by
            apply div_le_div_of_nonneg_left _ hmpos
            · rw [hcardnon, hn]; linarith
            · apply mul_nonneg (by linarith); linarith)
    (div_nonneg hσ0 hm'pos.le)
    (by linarith)
  linarith [hchain, hT'bound, hTD]

/-- The certificate forces. -/
theorem forcesOn_check (D r N₀ : ℕ) (h : check D r N₀ = true) : ForcesOn N₀ 3 (D + 1) := by
  simp only [check, decide_eq_true_eq] at h
  obtain ⟨hD, hN, hslope, hineq⟩ := h
  have hm1 : 1 ≤ N₀ - D - 1 := by clear hineq hslope; omega
  have hmN : (((N₀ - D - 1 : ℕ)) : ℚ) = (N₀ : ℚ) - 1 - D := by
    clear hineq hslope
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hXN : ((D * (N₀ - 2 * D) : ℕ) : ℚ) = (D : ℚ) * (N₀ - 2 * D) := by
    clear hineq hslope
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  have hsl := slope_pos r D hslope
  intro V _ _ G hcard
  classical
  by_contra hcon
  obtain ⟨hS, hT⟩ := not_or.mp hcon
  have htf : G.CliqueFree 3 := not_exists.mp hS
  have hT' : ∀ T : Finset V, ¬ Gᶜ.IsNClique (D + 1) T := not_exists.mp hT
  have hind : ∀ T : Finset V, G.IsIndepSet (T : Set V) → T.card ≤ D := by
    intro T hTind
    by_contra h
    obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq (Nat.lt_of_not_le h)
    refine hT' T' ⟨?_, hT'card⟩
    rw [isClique_compl]
    exact hTind.mono (Finset.coe_subset.mpr hT'T)
  have hq := q_le_of_ramsey G D r N₀ hD hN hsl hcard htf hind
  rw [a_eq r, del_succ_eq r, ← hmN, ← hXN] at hq
  exact check_arith D (N₀ - D - 1) (D * (N₀ - 2 * D)) _ _ _ hD hm1
    (shearer_pos (r + 1)).2 hineq hq

theorem forcesOn_certified (k N₀ : ℕ) (hk : 1 ≤ k) (h : certified k N₀ = true) :
    ForcesOn N₀ 3 k := by
  unfold certified at h
  rw [List.any_eq_true] at h
  obtain ⟨r, _, hr⟩ := h
  have h' : ForcesOn N₀ 3 (k - 1 + 1) := forcesOn_check (k - 1) r N₀ hr
  rwa [Nat.sub_add_cancel hk] at h'

theorem forcesOn_v (k : ℕ) (hk : 2 ≤ k) : ForcesOn (v k) 3 k := by
  have hV : ForcesOn (SqueezeBench.Ramsey3.Upper.V003.v k) 3 k :=
    SqueezeBench.Ramsey3.Upper.V003.forcesOn_v k hk
  have hk1 : 1 ≤ k := by omega
  show ForcesOn (if certified k (SqueezeBench.Ramsey3.Upper.V003.v k - 3)
      then SqueezeBench.Ramsey3.Upper.V003.v k - 3
      else if certified k (SqueezeBench.Ramsey3.Upper.V003.v k - 2)
      then SqueezeBench.Ramsey3.Upper.V003.v k - 2
      else if certified k (SqueezeBench.Ramsey3.Upper.V003.v k - 1)
      then SqueezeBench.Ramsey3.Upper.V003.v k - 1
      else SqueezeBench.Ramsey3.Upper.V003.v k) 3 k
  split_ifs with h1 h2 h3
  · exact forcesOn_certified k _ hk1 h1
  · exact forcesOn_certified k _ hk1 h2
  · exact forcesOn_certified k _ hk1 h3
  · exact hV

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f v := by
  intro k
  rcases Nat.lt_or_ge k SqueezeBench.Ramsey3.nMin with h | h
  · rw [SqueezeBench.Ramsey3.f, if_pos h]
    exact Nat.zero_le _
  · exact SqueezeBench.Ramsey3.f_le_of_forces h (Ramsey.forces_of_forcesOn (forcesOn_v k h))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Ramsey3.Upper.V003.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey3.Upper.V003.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Upper.V003.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 12) (by decide) (by decide)

end SqueezeBench.Ramsey3.Upper.V004
