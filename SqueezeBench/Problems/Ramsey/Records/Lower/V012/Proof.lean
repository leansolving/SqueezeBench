import SqueezeBench.Problems.Ramsey.Records.Lower.V012.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V011.Proof

/-! Record V012 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V012.lean`. Spencer's bound in its exact form: the symmetric
Lovász Local Lemma with the condition `e · p · (d + 1) ≤ 1` instead of V010's `4pd ≤ 1`.
The induction is V010's with the product bound in place of the union bound: adding the
dependent sets to the conditioning family one at a time, each keeps at least the fraction
`d/(d+1)` of the colourings by the induction hypothesis, so `|B_Y| · (d+1)^r ≥ d^r · |B_{Y₂}|`
for `r ≤ d` dependent sets; the cleared condition `2 · (d+1)^(d+1) ≤ 2^C(n,2) · d^d` then
gives `|A_S ∩ B_Y| · (d+1) ≤ |B_Y|`. That condition follows from the record's predicate
through `(1 + 1/d)^d ≤ e < 2718281829/10^9`, the only real-analysis step
(`Real.add_one_le_exp`, `Real.exp_one_lt_d9`). V010's events, fibre count, independence,
dependency count and V006's graph are reused unchanged. -/
namespace SqueezeBench.Ramsey.Lower.V012

open SqueezeBench SimpleGraph Finset

variable {N : ℕ}

/-! ## The local lemma in its exact symmetric form -/

-- Adding one set to the conditioning family loses at most the fraction `1/(d+1)`.
theorem card_avoid_insert {Y : Finset (Finset (Fin N))} {T : Finset (Fin N)} (_hT : T ∉ Y) :
    (V010.avoid (insert T Y)).card + (V010.bad T ∩ V010.avoid Y).card = (V010.avoid Y).card := by
  have heq : V010.avoid (insert T Y) = V010.avoid Y \ (V010.bad T ∩ V010.avoid Y) := by
    ext c
    simp only [V010.mem_avoid, Finset.mem_sdiff, Finset.mem_inter, V010.bad, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp]
    tauto
  rw [heq, Finset.card_sdiff_of_subset Finset.inter_subset_right]
  have := Finset.card_le_card (Finset.inter_subset_right (s₁ := V010.bad T) (s₂ := V010.avoid Y))
  omega

-- Main induction: `|A_S ∩ B_Y| · (d + 1) ≤ |B_Y|` for every family `Y`, given
-- `2 · (d+1)^(d+1) ≤ 2^C · d^d` (the cleared form of `e · p · (d+1) ≤ 1`).
theorem main_ind {n d : ℕ} (hd1 : 1 ≤ d)
    (hcond : 2 * (d + 1) ^ (d + 1) ≤ 2 ^ n.choose 2 * d ^ d)
    (hcount : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ,
      (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ d) :
    ∀ k, ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ, Y.card ≤ k →
      (V010.bad S ∩ V010.avoid Y).card * (d + 1) ≤ (V010.avoid Y).card := by
  intro k
  induction k with
  | zero =>
    intro S hS Y _ hYk
    have hY0 : Y = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hY0
    have h := V010.card_bad_inter_le (S := S) (B := V010.avoid ∅)
      (fun c c' _ => by simp [V010.mem_avoid])
    rw [(Finset.mem_powersetCard.mp hS).2] at h
    -- `x · 2^C ≤ 2y` and `2 (d+1)^(d+1) ≤ 2^C d^d` give `x (d+1) ≤ y`
    have hpos : 0 < 2 ^ n.choose 2 * d ^ d := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (V010.bad S ∩ V010.avoid ∅).card * (d + 1) * (2 ^ n.choose 2 * d ^ d)
        = (V010.bad S ∩ V010.avoid ∅).card * 2 ^ n.choose 2 * ((d + 1) * d ^ d) := by ring
      _ ≤ 2 * (V010.avoid ∅).card * ((d + 1) * d ^ d) := Nat.mul_le_mul_right _ h
      _ ≤ (V010.avoid ∅).card * (2 * (d + 1) ^ (d + 1)) := by
          have : (d + 1) * d ^ d ≤ (d + 1) ^ (d + 1) := by
            calc (d + 1) * d ^ d = d ^ d * (d + 1) := Nat.mul_comm _ _
              _ ≤ (d + 1) ^ d * (d + 1) :=
                  Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ d) d)
              _ = (d + 1) ^ (d + 1) := (pow_succ _ _).symm
          calc 2 * (V010.avoid ∅).card * ((d + 1) * d ^ d)
              ≤ 2 * (V010.avoid ∅).card * (d + 1) ^ (d + 1) := Nat.mul_le_mul_left _ this
            _ = (V010.avoid ∅).card * (2 * (d + 1) ^ (d + 1)) := by ring
      _ ≤ (V010.avoid ∅).card * (2 ^ n.choose 2 * d ^ d) := Nat.mul_le_mul_left _ hcond
  | succ k ih =>
    intro S hS Y hY hYk
    have hSn := (Finset.mem_powersetCard.mp hS).2
    have hdet : V010.DetOff S (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))) :=
      V010.detOff_avoid (fun T hT => by have := (Finset.mem_filter.mp hT).2; omega)
    have hA := V010.card_bad_inter_le hdet
    rw [hSn] at hA
    have hY2 : Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ⊆ Y := Finset.filter_subset _ _
    have hY1 : Y.filter (fun T => 2 ≤ (T ∩ S).card) ⊆ Y := Finset.filter_subset _ _
    have hle1 : (V010.bad S ∩ V010.avoid Y).card ≤
        (V010.bad S ∩ V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card :=
      Finset.card_le_card (Finset.inter_subset_inter_left (V010.avoid_anti hY2))
    have hsplit := Finset.card_filter_add_card_filter_not (s := Y) (p := fun T => 2 ≤ (T ∩ S).card)
    have hdisj : Disjoint (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))
        (Y.filter (fun T => 2 ≤ (T ∩ S).card)) := by
      rw [Finset.disjoint_left]
      intro T h1 h2
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    -- the product bound over the dependent members, added one at a time
    have hprod : ∀ U ⊆ Y.filter (fun T => 2 ≤ (T ∩ S).card),
        d ^ U.card * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card ≤
        (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card * (d + 1) ^ U.card := by
      intro U
      induction U using Finset.induction_on with
      | empty => intro _; simp
      | insert T U hTU ihU =>
        intro hU
        have hU' : U ⊆ Y.filter (fun T => 2 ≤ (T ∩ S).card) :=
          subset_trans (Finset.subset_insert _ _) hU
        have hT : T ∈ Y.filter (fun T => 2 ≤ (T ∩ S).card) := hU (Finset.mem_insert_self _ _)
        have hTY2 : T ∉ Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U := by
          rw [Finset.mem_union, not_or]
          exact ⟨fun h => (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hT).2, hTU⟩
        have hUcard : U.card + 1 ≤ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card := by
          have := Finset.card_le_card hU
          rw [Finset.card_insert_of_notMem hTU] at this
          exact this
        have hcond' : (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U).card ≤ k := by
          have := Finset.card_union_le (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) U
          omega
        have hsub : Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U ⊆ powersetCard n univ :=
          Finset.union_subset (subset_trans hY2 hY) (subset_trans (subset_trans hU' hY1) hY)
        have hstep := ih T (hY (Finset.mem_filter.mp hT).1) _ hsub hcond'
        have hins := card_avoid_insert (Y := Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U) hTY2
        rw [← Finset.union_insert] at hins
        have ihU' := ihU hU'
        rw [Finset.card_insert_of_notMem hTU, pow_succ, pow_succ]
        -- from `hins` and `hstep`: `d · |B_{Y₂∪U}| ≤ (d+1) · |B_{Y₂ ∪ insert T U}|`
        have hkey : d * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card ≤
            (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ insert T U)).card * (d + 1) := by
          have h1 : (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card * (d + 1) =
              (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ insert T U)).card * (d + 1) +
              (V010.bad T ∩ V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card * (d + 1) := by
            rw [← Nat.add_mul, hins]
          have h2 : (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card * (d + 1) =
              d * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card +
              (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card := by ring
          omega
        calc d ^ U.card * d * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card
            = d * (d ^ U.card * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) := by
              ring
          _ ≤ d * ((V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card *
                (d + 1) ^ U.card) := Nat.mul_le_mul_left _ ihU'
          _ = (d * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ U)).card) *
                (d + 1) ^ U.card := by ring
          _ ≤ ((V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ insert T U)).card * (d + 1)) *
                (d + 1) ^ U.card := Nat.mul_le_mul_right _ hkey
          _ = (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ∪ insert T U)).card *
                ((d + 1) ^ U.card * (d + 1)) := by ring
    have hfull := hprod _ (Finset.Subset.refl _)
    rw [Finset.union_comm, Finset.filter_union_filter_neg_eq] at hfull
    have hr : (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ d := hcount S hS Y hY
    -- `B₂ · d^d ≤ B · (d+1)^d` from the product bound and `r ≤ d`
    have hBd : (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card * d ^ d ≤
        (V010.avoid Y).card * (d + 1) ^ d := by
      have e1 : d ^ d = d ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card *
          d ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) := by
        rw [← pow_add, Nat.add_sub_cancel' hr]
      have e2 : (d + 1) ^ d = (d + 1) ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card *
          (d + 1) ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) := by
        rw [← pow_add, Nat.add_sub_cancel' hr]
      rw [e1, e2]
      calc (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card *
            (d ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card *
              d ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card))
          = (d ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card *
              (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) *
              d ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) := by ring
        _ ≤ ((V010.avoid Y).card * (d + 1) ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) *
              d ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) :=
            Nat.mul_le_mul_right _ hfull
        _ ≤ ((V010.avoid Y).card * (d + 1) ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) *
              (d + 1) ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ d) _)
        _ = (V010.avoid Y).card * ((d + 1) ^ (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card *
              (d + 1) ^ (d - (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card)) := by ring
    have hpos : 0 < 2 ^ n.choose 2 * d ^ d := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (V010.bad S ∩ V010.avoid Y).card * (d + 1) * (2 ^ n.choose 2 * d ^ d)
        = ((V010.bad S ∩ V010.avoid Y).card * 2 ^ n.choose 2) * ((d + 1) * d ^ d) := by ring
      _ ≤ ((V010.bad S ∩ V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card *
            2 ^ n.choose 2) * ((d + 1) * d ^ d) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle1)
      _ ≤ (2 * (V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) *
            ((d + 1) * d ^ d) := Nat.mul_le_mul_right _ hA
      _ = 2 * (d + 1) * ((V010.avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card * d ^ d) := by
          ring
      _ ≤ 2 * (d + 1) * ((V010.avoid Y).card * (d + 1) ^ d) := Nat.mul_le_mul_left _ hBd
      _ = (V010.avoid Y).card * (2 * (d + 1) ^ (d + 1)) := by ring
      _ ≤ (V010.avoid Y).card * (2 ^ n.choose 2 * d ^ d) := Nat.mul_le_mul_left _ hcond

-- Positivity: each added set keeps at least the fraction `d/(d+1)`, positive as `d ≥ 1`.
theorem avoid_pos {n d : ℕ} (hd1 : 1 ≤ d)
    (hcond : 2 * (d + 1) ^ (d + 1) ≤ 2 ^ n.choose 2 * d ^ d)
    (hcount : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ,
      (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ d) :
    ∀ Y ⊆ powersetCard n (univ : Finset (Fin N)), 0 < (V010.avoid Y).card := by
  intro Y
  induction Y using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.card_pos]
    exact ⟨fun _ => true, V010.mem_avoid.mpr (fun T hT => absurd hT (Finset.notMem_empty _))⟩
  | insert T Y hTY ih =>
    intro hY
    have hY' : Y ⊆ powersetCard n univ := subset_trans (Finset.subset_insert _ _) hY
    have hT : T ∈ powersetCard n univ := hY (Finset.mem_insert_self _ _)
    have hpos := ih hY'
    have hbound := main_ind hd1 hcond hcount Y.card T hT Y hY' le_rfl
    have hins := card_avoid_insert hTY
    have h2 : (V010.bad T ∩ V010.avoid Y).card * 2 ≤ (V010.bad T ∩ V010.avoid Y).card * (d + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## The real-analysis bridge: `(1 + 1/d)^d ≤ e < 2718281829 / 10^9` -/

theorem e_bridge {d C : ℕ} (hd : 1 ≤ d) (h : 2 * (d + 1) * 2718281829 ≤ 2 ^ C * 10 ^ 9) :
    2 * (d + 1) ^ (d + 1) ≤ 2 ^ C * d ^ d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((d : ℝ) + 1) ^ d ≤ (d : ℝ) ^ d * Real.exp 1 := by
    have hsplit : (d : ℝ) + 1 = d * (1 + 1 / d) := by field_simp
    rw [hsplit, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 : (1 + 1 / (d : ℝ)) ≤ Real.exp (1 / d) := by
      have := Real.add_one_le_exp (1 / (d : ℝ)); linarith
    calc (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp (1 / d) ^ d := pow_le_pow_left₀ (by positivity) h2 d
      _ = Real.exp (d * (1 / d)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp 1 := by rw [mul_one_div_cancel (ne_of_gt hd')]
  have he : Real.exp 1 ≤ 2718281829 / 10 ^ 9 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hh : (2 : ℝ) * (d + 1) * 2718281829 ≤ 2 ^ C * 10 ^ 9 := by exact_mod_cast h
  have hR : (2 : ℝ) * (d + 1) ^ (d + 1) ≤ 2 ^ C * d ^ d := by
    calc (2 : ℝ) * (d + 1) ^ (d + 1) = 2 * (d + 1) * (d + 1) ^ d := by ring
      _ ≤ 2 * (d + 1) * (d ^ d * Real.exp 1) := by gcongr
      _ ≤ 2 * (d + 1) * (d ^ d * (2718281829 / 10 ^ 9)) := by gcongr
      _ = (2 * (d + 1) * 2718281829) * d ^ d / 10 ^ 9 := by ring
      _ ≤ (2 ^ C * 10 ^ 9) * d ^ d / 10 ^ 9 := by gcongr
      _ = 2 ^ C * d ^ d := by field_simp
  exact_mod_cast hR

/-! ## From the condition to `¬ Forces` -/

theorem not_forces_small {n : ℕ} (hn : 1 ≤ n) (hN : N < n) : ¬ Forces N n n := by
  intro hF
  rcases hF ⊥ with ⟨S, hS⟩ | ⟨T, hT⟩
  · have := Finset.card_le_univ S
    rw [hS.card_eq, Fintype.card_fin] at this
    omega
  · have := Finset.card_le_univ T
    rw [hT.card_eq, Fintype.card_fin] at this
    omega

theorem not_forces {n : ℕ} (hn3 : 3 ≤ n) (hNn : n ≤ N)
    (h : 2 * (n.choose 2 * (N - 2).choose (n - 2) + 1) * 2718281829 ≤
      2 ^ n.choose 2 * 10 ^ 9) : ¬ Forces N n n := by
  intro hF
  have hd1 : 1 ≤ n.choose 2 * (N - 2).choose (n - 2) :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hcond := e_bridge hd1 h
  have hcount : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ,
      (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ n.choose 2 * (N - 2).choose (n - 2) :=
    fun S hS Y hY => V010.card_dep_le (Finset.mem_powersetCard.mp hS).2 hY
  have hpos := avoid_pos hd1 hcond hcount (powersetCard n univ) (Finset.Subset.refl _)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  rw [V010.mem_avoid] at hc
  rcases hF (V006.graphOf c) with ⟨S, hS⟩ | ⟨T, hT⟩
  · refine hc S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.card_eq⟩) (Or.inl ?_)
    intro p hp
    rw [V006.mem_pairs] at hp
    have hadj := V006.graphOf_adj.mp (hS.isClique hp.1 hp.2.1 (ne_of_lt hp.2.2))
    rw [min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    exact hadj.2
  · refine hc T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT.card_eq⟩) (Or.inr ?_)
    intro p hp
    rw [V006.mem_pairs] at hp
    have hadj := hT.isClique hp.1 hp.2.1 (ne_of_lt hp.2.2)
    rw [compl_adj, V006.graphOf_adj] at hadj
    rw [min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    by_contra hcp
    exact hadj.2 ⟨hadj.1, by simpa using hcp⟩

/-! ## The bound -/

-- Any `M` satisfying the record's predicate gives `f n ≥ M + 1`.
theorem main {n M : ℕ} (hn3 : 3 ≤ n)
    (hM : 2 * (n.choose 2 * (M - 2) ^ (n - 2) + (n - 2).factorial) * 2718281829 ≤
      2 ^ n.choose 2 * (n - 2).factorial * 10 ^ 9) : M + 1 ≤ f n := by
  have hn : nMin ≤ n := by simp [nMin]; omega
  refine le_f hn ?_
  intro N hN
  by_contra hcon
  have hNM : N ≤ M := by omega
  rcases Nat.lt_or_ge N n with hlt | hge
  · exact not_forces_small (by omega) hlt hN
  · refine not_forces hn3 hge ?_ hN
    have h1 : (n - 2).factorial * (N - 2).choose (n - 2) ≤ (N - 2) ^ (n - 2) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    have h2 : (N - 2) ^ (n - 2) ≤ (M - 2) ^ (n - 2) :=
      Nat.pow_le_pow_left (Nat.sub_le_sub_right hNM 2) _
    have h3 : (n - 2).factorial * (2 * (n.choose 2 * (N - 2).choose (n - 2) + 1) * 2718281829) ≤
        (n - 2).factorial * (2 ^ n.choose 2 * 10 ^ 9) := by
      calc (n - 2).factorial * (2 * (n.choose 2 * (N - 2).choose (n - 2) + 1) * 2718281829)
          = 2 * (n.choose 2 * ((n - 2).factorial * (N - 2).choose (n - 2)) + (n - 2).factorial) *
              2718281829 := by ring
        _ ≤ 2 * (n.choose 2 * (N - 2) ^ (n - 2) + (n - 2).factorial) * 2718281829 := by
            gcongr
        _ ≤ 2 * (n.choose 2 * (M - 2) ^ (n - 2) + (n - 2).factorial) * 2718281829 := by
            gcongr
        _ ≤ 2 ^ n.choose 2 * (n - 2).factorial * 10 ^ 9 := hM
        _ = (n - 2).factorial * (2 ^ n.choose 2 * 10 ^ 9) := by ring
    exact Nat.le_of_mul_le_mul_left h3 (Nat.factorial_pos _)

/-! ## The record -/

theorem bsearch_ok {n F K : ℕ} : ∀ fuel lo hi,
    2 * (n * (n - 1) / 2 * (lo - 2) ^ (n - 2) + F) * 2718281829 ≤ K →
    2 * (n * (n - 1) / 2 * (bsearch n F K fuel lo hi - 2) ^ (n - 2) + F) * 2718281829 ≤ K := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h; simpa [bsearch] using h
  | succ fuel ih =>
    intro lo hi h
    rw [bsearch]
    split_ifs with h1 h2
    · exact h
    · exact ih _ _ h2
    · exact ih _ _ h

theorem spencer_ok {n : ℕ} (hn3 : 3 ≤ n) :
    2 * (n.choose 2 * (spencer n - 2) ^ (n - 2) + (n - 2).factorial) * 2718281829 ≤
      2 ^ n.choose 2 * (n - 2).factorial * 10 ^ 9 := by
  have h8 : 8 ≤ 2 ^ (n * (n - 1) / 2) := by
    have h3 : 3 ≤ n.choose 2 :=
      calc 3 = Nat.choose 3 2 := by decide
        _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn3
    rw [← Nat.choose_two_right]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n.choose 2 := Nat.pow_le_pow_right (by norm_num) h3
  have h0 : 2 * (n * (n - 1) / 2 * (0 - 2) ^ (n - 2) + V006.fact (n - 2)) * 2718281829 ≤
      2 ^ (n * (n - 1) / 2) * V006.fact (n - 2) * 10 ^ 9 := by
    rw [Nat.zero_sub, zero_pow (by omega), Nat.mul_zero, Nat.zero_add]
    calc 2 * V006.fact (n - 2) * 2718281829 = V006.fact (n - 2) * (2 * 2718281829) := by ring
      _ ≤ V006.fact (n - 2) * (2 ^ (n * (n - 1) / 2) * 10 ^ 9) := by
          refine Nat.mul_le_mul_left _ ?_
          calc 2 * 2718281829 ≤ 8 * 10 ^ 9 := by norm_num
            _ ≤ 2 ^ (n * (n - 1) / 2) * 10 ^ 9 := Nat.mul_le_mul_right _ h8
      _ = 2 ^ (n * (n - 1) / 2) * V006.fact (n - 2) * 10 ^ 9 := by ring
  have := bsearch_ok (n + 1) 0 (2 ^ n) h0
  change 2 * (n * (n - 1) / 2 * (spencer n - 2) ^ (n - 2) + V006.fact (n - 2)) * 2718281829 ≤
    2 ^ (n * (n - 1) / 2) * V006.fact (n - 2) * 10 ^ 9 at this
  rw [V006.fact_eq, ← Nat.choose_two_right] at this
  exact this

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v :=
  pin_lowerBoundHolds (fun _ hn => main hn (spencer_ok hn))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V011.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V011.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V011.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 20) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V012
