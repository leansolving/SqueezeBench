import SqueezeBench.Problems.Ramsey3.Records.Lower.V003.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V002.Proof

-- Record V003 for Ramsey3, lower direction, by baseline claude-opus-5.
--
-- Witness graph: the blow-up of the circulant `C₁₃(±1,±5)`, the extremal graph for `R(3,5)`.
-- Vertex `x` of `Fin N` carries the residue `x % 13`, and two vertices are joined when their
-- residues differ by `±1` or `±5` mod 13.
--
-- Triangle-free: three differences from `{1,5,8,12}` never sum to `0` mod 13.
--
-- Independence number `4q` for `N ≤ 13q`: the residues used by an independent set form an
-- independent set of `C₁₃(±1,±5)`, which has at most `4` elements, and each residue class of
-- `Fin N` has at most `q` members. That `C₁₃(±1,±5)` has no independent set of five residues
-- is proved from the cyclic gaps: five residues in cyclic order have gaps `≥ 2` (difference `1`
-- is an edge) summing to `13` and different from `5`, hence all in `[2,4]`, and no two
-- consecutive gaps sum to `5` (difference `5` is an edge). The only gap multisets left are
-- `(4,3,2,2,2)` and `(3,3,3,2,2)`, and in each the single `3`, resp. each `2`, would need two
-- distinct neighbours that are not its forbidden partner. `omega` closes this.
--
-- Taking `q = ⌊(k-1)/4⌋` gives independence number `4q ≤ k-1` on `13q` vertices, so
-- `R(3,k) ≥ 13⌊(k-1)/4⌋ + 1`, ratio `13/4` against `3` for V002. V002 is larger at the small
-- `k`, so the two are folded with `maxWith`.

namespace SqueezeBench.Ramsey3.Lower.V003

open SqueezeBench SimpleGraph

-- Adjacency in `C₁₃(±1,±5)`, read off the residues so that `omega` sees it.
def radj (x y : ℕ) : Prop :=
  (x + 1) % 13 = y % 13 ∨ (x + 5) % 13 = y % 13 ∨ (y + 1) % 13 = x % 13 ∨ (y + 5) % 13 = x % 13

theorem radj_symm {x y : ℕ} (h : radj x y) : radj y x := by
  unfold radj at h ⊢; tauto

theorem radj_irrefl (x : ℕ) : ¬ radj x x := by
  unfold radj; omega

-- Adjacency only depends on the residues.
theorem radj_mod {x y : ℕ} (h : radj (x % 13) (y % 13)) : radj x y := by
  unfold radj at h ⊢; omega

-- Three mutually adjacent residues are impossible.
theorem radj_no_triangle {x y z : ℕ} (h1 : radj x y) (h2 : radj x z) (h3 : radj y z) : False := by
  unfold radj at h1 h2 h3; omega

-- A non-edge between two residues below 13 forbids the four differences of the circulant.
theorem not_radj_diff {x y : ℕ} (hxy : x < y) (hy : y < 13) (h : ¬ radj x y) :
    y - x ≠ 1 ∧ y - x ≠ 5 ∧ y - x ≠ 8 ∧ y - x ≠ 12 := by
  unfold radj at h; omega

-- The gap contradiction: five gaps in `[2,4]` summing to `13` always have two consecutive ones
-- summing to `5`.
theorem gaps_absurd {g₁ g₂ g₃ g₄ g₅ : ℕ} (hs : g₁ + g₂ + g₃ + g₄ + g₅ = 13)
    (b₁ : 2 ≤ g₁ ∧ g₁ ≤ 4) (b₂ : 2 ≤ g₂ ∧ g₂ ≤ 4) (b₃ : 2 ≤ g₃ ∧ g₃ ≤ 4)
    (b₄ : 2 ≤ g₄ ∧ g₄ ≤ 4) (b₅ : 2 ≤ g₅ ∧ g₅ ≤ 4)
    (p₁ : g₁ + g₂ ≠ 5) (p₂ : g₂ + g₃ ≠ 5) (p₃ : g₃ + g₄ ≠ 5) (p₄ : g₄ + g₅ ≠ 5)
    (p₅ : g₅ + g₁ ≠ 5) : False := by
  omega

-- No five residues are pairwise non-adjacent.
theorem no_indep_five {a b c d e : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (he : e < 13) (nab : ¬ radj a b) (nac : ¬ radj a c) (nad : ¬ radj a d) (nae : ¬ radj a e)
    (nbc : ¬ radj b c) (nbd : ¬ radj b d) (nbe : ¬ radj b e) (ncd : ¬ radj c d)
    (nce : ¬ radj c e) (nde : ¬ radj d e) : False := by
  obtain ⟨ab1, ab5, -, -⟩ := not_radj_diff hab (by omega) nab
  obtain ⟨-, ac5, -, -⟩ := not_radj_diff (show a < c by omega) (by omega) nac
  obtain ⟨-, -, ad8, -⟩ := not_radj_diff (show a < d by omega) (by omega) nad
  obtain ⟨-, -, ae8, ae12⟩ := not_radj_diff (show a < e by omega) he nae
  obtain ⟨bc1, bc5, -, -⟩ := not_radj_diff hbc (by omega) nbc
  obtain ⟨-, bd5, -, -⟩ := not_radj_diff (show b < d by omega) (by omega) nbd
  obtain ⟨-, -, be8, -⟩ := not_radj_diff (show b < e by omega) he nbe
  obtain ⟨cd1, cd5, -, -⟩ := not_radj_diff hcd (by omega) ncd
  obtain ⟨-, ce5, -, -⟩ := not_radj_diff (show c < e by omega) he nce
  obtain ⟨de1, de5, -, -⟩ := not_radj_diff hde he nde
  exact gaps_absurd (g₁ := b - a) (g₂ := c - b) (g₃ := d - c) (g₄ := e - d) (g₅ := 13 - e + a)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)

-- The independent sets of `C₁₃(±1,±5)` have at most four elements.
theorem indep_residues_card_le {R : Finset ℕ} (hR : ∀ r ∈ R, r < 13)
    (hind : ∀ x ∈ R, ∀ y ∈ R, ¬ radj x y) : R.card ≤ 4 := by
  by_contra hc
  obtain ⟨S, hSR, hS⟩ := Finset.exists_subset_card_eq (show 5 ≤ R.card by omega)
  set g := S.orderIsoOfFin hS with hgdef
  have hm : ∀ i : Fin 5, ((g i : ℕ)) ∈ R := fun i => hSR (g i).2
  have hlt : ∀ i j : Fin 5, i < j → ((g i : ℕ)) < ((g j : ℕ)) := by
    intro i j hij
    exact_mod_cast (g.lt_iff_lt).mpr hij
  exact no_indep_five (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide))
    (hlt 3 4 (by decide)) (hR _ (hm 4))
    (hind _ (hm 0) _ (hm 1)) (hind _ (hm 0) _ (hm 2)) (hind _ (hm 0) _ (hm 3))
    (hind _ (hm 0) _ (hm 4)) (hind _ (hm 1) _ (hm 2)) (hind _ (hm 1) _ (hm 3))
    (hind _ (hm 1) _ (hm 4)) (hind _ (hm 2) _ (hm 3)) (hind _ (hm 2) _ (hm 4))
    (hind _ (hm 3) _ (hm 4))

-- The blow-up, restricted to the first `N` vertices.
def cg (N : ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun x y : Fin N => radj (x : ℕ) (y : ℕ))

theorem cg_adj {N : ℕ} (x y : Fin N) : (cg N).Adj x y ↔ radj (x : ℕ) (y : ℕ) := by
  unfold cg
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact radj_symm h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact radj_irrefl _ h

theorem cg_cliqueFree_three {N : ℕ} : (cg N).CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  exact radj_no_triangle ((cg_adj _ _).mp (hS.isClique (by simp) (by simp) hab))
    ((cg_adj _ _).mp (hS.isClique (by simp) (by simp) hac))
    ((cg_adj _ _).mp (hS.isClique (by simp) (by simp) hbc))

-- An independent set meets at most four residue classes, each of size at most `q`.
theorem indep_card_le {q N : ℕ} (hN : N ≤ 13 * q) {T : Finset (Fin N)}
    (hT : ∀ x ∈ T, ∀ y ∈ T, ¬ radj (x : ℕ) (y : ℕ)) : T.card ≤ 4 * q := by
  have hfib : ∀ r ∈ T.image (fun x : Fin N => (x : ℕ) % 13),
      (T.filter (fun x : Fin N => (x : ℕ) % 13 = r)).card ≤ q := by
    intro r _
    have hmaps : ∀ x ∈ T.filter (fun x : Fin N => (x : ℕ) % 13 = r),
        (x : ℕ) / 13 ∈ Finset.range q := by
      intro x hx
      have h1 : (x : ℕ) < N := x.isLt
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : Fin N => (x : ℕ) / 13)
        ↑(T.filter (fun x : Fin N => (x : ℕ) % 13 = r)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      simp only at hxy
      exact Fin.ext (by omega)
    calc (T.filter (fun x : Fin N => (x : ℕ) % 13 = r)).card
        ≤ (Finset.range q).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = q := Finset.card_range _
  have himg : (T.image (fun x : Fin N => (x : ℕ) % 13)).card ≤ 4 := by
    apply indep_residues_card_le
    · intro r hr
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hr
      omega
    · intro r hr s hs hrs
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
      exact hT x hx y hy (radj_mod hrs)
  calc T.card ≤ q * (T.image (fun x : Fin N => (x : ℕ) % 13)).card :=
        Finset.card_le_mul_card_image _ _ hfib
    _ ≤ q * 4 := Nat.mul_le_mul_left _ himg
    _ = 4 * q := Nat.mul_comm _ _

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) :
    13 * ((k - 1) / 4) + 1 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  by_contra hcon
  have hN : N ≤ 13 * ((k - 1) / 4) := by omega
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
    have hcard := indep_card_le hN hind
    rw [hT.card_eq] at hcard
    omega

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f v :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  maxWith_valid SqueezeBench.Ramsey3.Lower.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V002.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V002.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Ramsey3.Lower.V003
