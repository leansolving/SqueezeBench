import SqueezeBench.Problems.Ramsey3.Records.Lower.V001.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V000.Proof

-- Record V001 for Ramsey3, lower direction, by baseline claude-opus-5.
--
-- The witness graph is the balanced blow-up of the 5-cycle: on `Fin N` the vertex `x`
-- carries the residue `x % 5`, and two vertices are adjacent when their residues are
-- consecutive mod 5. It is triangle-free because `C₅` is, and an independent set uses
-- only residues that are pairwise non-consecutive, i.e. at most two of them.
--
-- With `N = ⌊5(k-1)/2⌋` the two residue classes of an independent set contribute at most
-- `k-1` vertices: when `k-1 = 2q` every class has `q` vertices, and when `k-1 = 2q+1`
-- only the classes `0` and `1` have `q+1`, and those two are adjacent in `C₅`, so at most
-- one of them is used. So no `N ≤ ⌊5(k-1)/2⌋` forces, and `R(3,k) ≥ ⌊5(k-1)/2⌋ + 1`.

namespace SqueezeBench.Ramsey3.Lower.V001

open SqueezeBench SimpleGraph

-- Adjacency of residues in the 5-cycle, read off any two naturals.
def cadj (a b : ℕ) : Prop := (a % 5 + 1) % 5 = b % 5 ∨ (b % 5 + 1) % 5 = a % 5

theorem cadj_irrefl (a : ℕ) : ¬ cadj a a := by
  unfold cadj; omega

-- `C₅` has no triangle.
theorem cadj_no_triangle {a b c : ℕ} (h1 : cadj a b) (h2 : cadj a c) (h3 : cadj b c) : False := by
  unfold cadj at h1 h2 h3; omega

-- `C₅` has no independent set of three distinct residues.
theorem cadj_no_indep_three {a b c : ℕ}
    (hab : a % 5 ≠ b % 5) (hac : a % 5 ≠ c % 5) (hbc : b % 5 ≠ c % 5)
    (n1 : ¬ cadj a b) (n2 : ¬ cadj a c) (n3 : ¬ cadj b c) : False := by
  unfold cadj at n1 n2 n3; push_neg at n1 n2 n3; omega

-- The blow-up of `C₅` on `Fin N`, with the residue classes mod `5` as the five parts.
def blowC5 (N : ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun x y : Fin N => ((x : ℕ) % 5 + 1) % 5 = (y : ℕ) % 5)

theorem blowC5_adj {N : ℕ} (x y : Fin N) :
    (blowC5 N).Adj x y ↔ cadj (x : ℕ) (y : ℕ) := by
  unfold blowC5 cadj
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    exact cadj_irrefl _ h

theorem blowC5_cliqueFree_three (N : ℕ) : (blowC5 N).CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  have h1 := hS.isClique (by simp) (by simp) hab
  have h2 := hS.isClique (by simp) (by simp) hac
  have h3 := hS.isClique (by simp) (by simp) hbc
  exact cadj_no_triangle ((blowC5_adj _ _).mp h1) ((blowC5_adj _ _).mp h2)
    ((blowC5_adj _ _).mp h3)

-- An independent set of the blow-up on at most `⌊5m/2⌋` vertices has at most `m` vertices.
-- The map `x ↦ 2 * (x / 5) + (0 if x is in the smallest used residue class, else 1)` is
-- injective on it and lands in `range m`.
theorem indep_card_le {m N : ℕ} (hN : N ≤ 5 * m / 2) {T : Finset (Fin N)}
    (hT : (blowC5 N)ᶜ.IsClique ↑T) : T.card ≤ m := by
  have hnadj : ∀ x ∈ T, ∀ y ∈ T, ¬ cadj (x : ℕ) (y : ℕ) := by
    intro x hx y hy h
    rcases eq_or_ne x y with rfl | hne
    · exact cadj_irrefl _ h
    · have hc := hT hx hy hne
      rw [compl_adj] at hc
      exact hc.2 ((blowC5_adj x y).mpr h)
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set R := T.image (fun x : Fin N => (x : ℕ) % 5) with hR
  have hRne : R.Nonempty := ⟨_, Finset.mem_image_of_mem _ hx₀⟩
  set s := R.min' hRne with hs
  have hsmem : s ∈ R := R.min'_mem hRne
  have hsle : ∀ x ∈ T, s ≤ (x : ℕ) % 5 := fun x hx => R.min'_le _ (Finset.mem_image_of_mem _ hx)
  -- at most two residues occur, so everything outside the class of `s` has one residue
  have htwo : ∀ x ∈ T, ∀ y ∈ T, (x : ℕ) % 5 ≠ s → (y : ℕ) % 5 ≠ s →
      (x : ℕ) % 5 = (y : ℕ) % 5 := by
    intro x hx y hy hxs hys
    by_contra hne
    obtain ⟨z, hz, hzs⟩ := Finset.mem_image.mp hsmem
    exact cadj_no_indep_three (a := (z : ℕ)) (b := (x : ℕ)) (c := (y : ℕ))
      (by omega) (by omega) hne (hnadj z hz x hx) (hnadj z hz y hy) (hnadj x hx y hy)
  -- residues `0` and `1` are adjacent, so a used one of them is the smallest used residue
  have hres : ∀ x ∈ T, (x : ℕ) % 5 < 2 → (x : ℕ) % 5 = s := by
    intro x hx hlt
    have h1 := hsle x hx
    obtain ⟨z, hz, hzs⟩ := Finset.mem_image.mp hsmem
    have hnz := hnadj z hz x hx
    unfold cadj at hnz
    push_neg at hnz
    omega
  have hmaps : ∀ x ∈ T,
      2 * ((x : ℕ) / 5) + (if (x : ℕ) % 5 = s then 0 else 1) ∈ Finset.range m := by
    intro x hx
    have hxN : (x : ℕ) < N := x.isLt
    rw [Finset.mem_range]
    split_ifs with hc
    · omega
    · have h2 : ¬ ((x : ℕ) % 5 < 2) := fun h => hc (hres x hx h)
      omega
  have hinj : Set.InjOn
      (fun x : Fin N => 2 * ((x : ℕ) / 5) + (if (x : ℕ) % 5 = s then 0 else 1)) ↑T := by
    intro x hx y hy hxy
    simp only at hxy
    split_ifs at hxy with hcx hcy hcy
    · exact Fin.ext (by omega)
    · omega
    · omega
    · have := htwo x hx y hy hcx hcy
      exact Fin.ext (by omega)
  calc T.card ≤ (Finset.range m).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = m := Finset.card_range m

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) :
    5 * (k - 1) / 2 + 1 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  by_contra hcon
  rcases h (blowC5 N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact blowC5_cliqueFree_three N S hS
  · have hcard := indep_card_le (m := k - 1) (N := N) (by omega) hT.isClique
    rw [hT.card_eq] at hcard
    omega

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V000.record record := by
  intro n
  simp only [record, SqueezeBench.Ramsey3.Lower.V000.record, pin, nMin]
  split_ifs with h
  · exact Nat.le_refl 0
  · omega

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V000.record record :=
  ⟨9, by decide, by decide⟩

end SqueezeBench.Ramsey3.Lower.V001
