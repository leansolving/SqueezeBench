import SqueezeBench.Problems.Ramsey3.Records.Lower.V004.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V003.Proof

-- Record V004 for Ramsey3, lower direction, by baseline claude-opus-5.
--
-- Same witness graph as V003 — the blow-up of `C₁₃(±1,±5)` on `Fin N`, vertex `x` carrying the
-- residue `x % 13` — but with `N = 13q + 2r` instead of `13q`, where `k - 1 = 4q + r`, `r < 4`.
-- Triangle-freeness and "an independent set meets at most four residue classes" are V003's
-- lemmas verbatim; only the count changes.
--
-- The `2r` residues `0, …, 2r-1` now carry `q + 1` vertices each, the other `13 - 2r` carry `q`.
-- An independent set of residues contains no two consecutive residues (difference `1` is an
-- edge), so `ρ ↦ ρ / 2` is injective on its intersection with the prefix `[0, 2r)` and lands in
-- `range r`: it meets the prefix in at most `r` classes. Splitting the independent set `T` by
-- whether its residue lies in the prefix gives
-- `|T| ≤ (q+1)·|I₁| + q·|I₂| = q·(|I₁|+|I₂|) + |I₁| ≤ 4q + r = k - 1`.
--
-- So `R(3,k) ≥ 13⌊(k-1)/4⌋ + 2((k-1) mod 4) + 1`, which beats V003 by `2r` at every `k` with
-- `k ≢ 1 (mod 4)` — three quarters of all `k`.

namespace SqueezeBench.Ramsey3.Lower.V004

open SqueezeBench SimpleGraph

open SqueezeBench.Ramsey3.Lower.V003 (radj radj_mod radj_irrefl not_radj_diff cg cg_adj
  cg_cliqueFree_three indep_residues_card_le)

-- An independent set of residues inside the prefix `[0, 2r)` has at most `r` elements: it has no
-- two consecutive residues, so `ρ ↦ ρ / 2` is injective on it.
theorem prefix_indep_card_le {r : ℕ} (hr : 2 * r ≤ 13) {R : Finset ℕ}
    (hR : ∀ x ∈ R, x < 2 * r) (hind : ∀ x ∈ R, ∀ y ∈ R, ¬ radj x y) : R.card ≤ r := by
  have hmaps : ∀ x ∈ R, x / 2 ∈ Finset.range r := by
    intro x hx
    have := hR x hx
    rw [Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun x : ℕ => x / 2) ↑R := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only at hxy
    have hx2 := hR x hx
    have hy2 := hR y hy
    by_contra hne
    rcases Nat.lt_or_ge x y with h | h
    · exact (not_radj_diff h (by omega) (hind x hx y hy)).1 (by omega)
    · exact (not_radj_diff (show y < x by omega) (by omega) (hind y hy x hx)).1 (by omega)
  calc R.card ≤ (Finset.range r).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = r := Finset.card_range _

-- The unbalanced count.
theorem indep_card_le {q r N : ℕ} (hr : 2 * r ≤ 13) (hN : N ≤ 13 * q + 2 * r) {T : Finset (Fin N)}
    (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ radj (x : ℕ) (y : ℕ)) : T.card ≤ 4 * q + r := by
  classical
  set p : Fin N → Prop := fun x => (x : ℕ) % 13 < 2 * r with hp
  set T₁ := T.filter p with hT₁
  set T₂ := T.filter (fun x => ¬ p x) with hT₂
  set I₁ := T₁.image (fun x : Fin N => (x : ℕ) % 13) with hI₁
  set I₂ := T₂.image (fun x : Fin N => (x : ℕ) % 13) with hI₂
  -- Fibres over the prefix have at most `q + 1` elements.
  have hfib₁ : ∀ ρ ∈ I₁, (T₁.filter (fun x : Fin N => (x : ℕ) % 13 = ρ)).card ≤ q + 1 := by
    intro ρ _
    have hmaps : ∀ x ∈ T₁.filter (fun x : Fin N => (x : ℕ) % 13 = ρ),
        (x : ℕ) / 13 ∈ Finset.range (q + 1) := by
      intro x _
      have h1 : (x : ℕ) < N := x.isLt
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : Fin N => (x : ℕ) / 13)
        ↑(T₁.filter (fun x : Fin N => (x : ℕ) % 13 = ρ)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      simp only at hxy
      exact Fin.ext (by omega)
    calc (T₁.filter (fun x : Fin N => (x : ℕ) % 13 = ρ)).card
        ≤ (Finset.range (q + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = q + 1 := Finset.card_range _
  -- Fibres outside it have at most `q`.
  have hfib₂ : ∀ ρ ∈ I₂, (T₂.filter (fun x : Fin N => (x : ℕ) % 13 = ρ)).card ≤ q := by
    intro ρ _
    have hmaps : ∀ x ∈ T₂.filter (fun x : Fin N => (x : ℕ) % 13 = ρ),
        (x : ℕ) / 13 ∈ Finset.range q := by
      intro x hx
      simp only [hT₂, Finset.mem_filter, hp, Nat.not_lt] at hx
      have h1 : (x : ℕ) < N := x.isLt
      have h2 : (x : ℕ) % 13 = ρ := hx.2
      have h3 : 2 * r ≤ (x : ℕ) % 13 := hx.1.2
      have h4 : (x : ℕ) = 13 * ((x : ℕ) / 13) + (x : ℕ) % 13 := (Nat.div_add_mod _ _).symm
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : Fin N => (x : ℕ) / 13)
        ↑(T₂.filter (fun x : Fin N => (x : ℕ) % 13 = ρ)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      simp only at hxy
      exact Fin.ext (by omega)
    calc (T₂.filter (fun x : Fin N => (x : ℕ) % 13 = ρ)).card
        ≤ (Finset.range q).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = q := Finset.card_range _
  have hc₁ : T₁.card ≤ (q + 1) * I₁.card := Finset.card_le_mul_card_image _ _ hfib₁
  have hc₂ : T₂.card ≤ q * I₂.card := Finset.card_le_mul_card_image _ _ hfib₂
  -- The residues of `T₁` are independent and lie in the prefix.
  have hind : ∀ (S : Finset (Fin N)), S ⊆ T → ∀ ρ ∈ S.image (fun x : Fin N => (x : ℕ) % 13),
      ∀ σ ∈ S.image (fun x : Fin N => (x : ℕ) % 13), ¬ radj ρ σ := by
    intro S hS ρ hρ σ hσ hrs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hσ
    exact hT x (hS hx) y (hS hy) (radj_mod hrs)
  have hI₁card : I₁.card ≤ r := by
    refine prefix_indep_card_le hr ?_ (hind T₁ (Finset.filter_subset _ _))
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hρ
    simp only [hT₁, Finset.mem_filter, hp] at hx
    exact hx.2
  -- The two residue sets are disjoint and together form the residues of `T`.
  have hdisj : Disjoint I₁ I₂ := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρ'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hρ'
    simp only [hT₁, Finset.mem_filter, hp] at hx
    simp only [hT₂, Finset.mem_filter, hp, Nat.not_lt] at hy
    omega
  have hunion : I₁ ∪ I₂ = T.image (fun x : Fin N => (x : ℕ) % 13) := by
    rw [hI₁, hI₂, ← Finset.image_union, hT₁, hT₂, Finset.filter_union_filter_neg_eq]
  have hsum : I₁.card + I₂.card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    refine indep_residues_card_le ?_ (hind T (subset_refl _))
    intro ρ hρ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hρ
    omega
  have hsplit : T₁.card + T₂.card = T.card := by
    rw [hT₁, hT₂]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  calc T.card = T₁.card + T₂.card := hsplit.symm
    _ ≤ (q + 1) * I₁.card + q * I₂.card := Nat.add_le_add hc₁ hc₂
    _ ≤ 4 * q + r := by nlinarith [hI₁card, hsum]

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) :
    13 * ((k - 1) / 4) + 2 * ((k - 1) % 4) + 1 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  have hmod : (k - 1) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hdm : k - 1 = 4 * ((k - 1) / 4) + (k - 1) % 4 := (Nat.div_add_mod _ _).symm
  by_contra hcon
  have hN : N ≤ 13 * ((k - 1) / 4) + 2 * ((k - 1) % 4) := by omega
  rcases h (cg N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact cg_cliqueFree_three S hS
  · have hind : ∀ x ∈ T, ∀ y ∈ T, ¬ radj (x : ℕ) (y : ℕ) := by
      intro x hx y hy
      rcases eq_or_ne x y with rfl | hne
      · exact radj_irrefl _
      · have hc := hT.isClique hx hy hne
        rw [compl_adj] at hc
        have h2 := hc.2
        rw [cg_adj] at h2
        exact h2
    have hcard := indep_card_le (by omega) hN hind
    rw [hT.card_eq] at hcard
    omega

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f v :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  maxWith_valid SqueezeBench.Ramsey3.Lower.V003.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V003.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V003.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 10) (by decide) (by decide)

end SqueezeBench.Ramsey3.Lower.V004
