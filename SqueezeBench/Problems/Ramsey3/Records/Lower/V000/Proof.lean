import SqueezeBench.Problems.Ramsey3.Records.Lower.V000.Def

/-!
# `R(3,k)` lower-bound record V000 — validity

The witness is the **parity graph** on `Fin N`: `x` and `y` are adjacent exactly when they have
different parity. It is the complete bipartite graph between the evens and the odds, written so
that it lives on `Fin N` directly and needs no re-indexing.

It is triangle-free because among any three vertices two share a parity, and those two are
therefore non-adjacent. A clique in its complement has *constant* parity, so `x ↦ x / 2` is
injective on it and it has at most `(N+1)/2` vertices. Taking `N = 2k-2` makes that `k-1`, so no
such `N` forces, and every `N` that does satisfies `2k-1 ≤ N`.
-/

namespace SqueezeBench.Ramsey3.Lower.V000

open SqueezeBench SimpleGraph

/-- Adjacency is difference of parity: the complete bipartite graph between evens and odds.
`symm` and `loopless` are left to `aesop_graph`. -/
def parityGraph (N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := (x : ℕ) % 2 ≠ (y : ℕ) % 2

@[simp] theorem parityGraph_adj {N : ℕ} (x y : Fin N) :
    (parityGraph N).Adj x y ↔ (x : ℕ) % 2 ≠ (y : ℕ) % 2 := Iff.rfl

/-- Among any three vertices two share a parity, so there is no triangle. -/
theorem parityGraph_cliqueFree_three (N : ℕ) : (parityGraph N).CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  have h1 := hS.isClique (by simp) (by simp) hab
  have h2 := hS.isClique (by simp) (by simp) hac
  have h3 := hS.isClique (by simp) (by simp) hbc
  simp only [parityGraph_adj] at h1 h2 h3
  omega

/-- A clique in the complement has constant parity, so `x ↦ x / 2` embeds it into
`range ((N+1)/2)`. -/
theorem parityGraph_compl_card {N : ℕ} {T : Finset (Fin N)}
    (hT : (parityGraph N)ᶜ.IsClique ↑T) : T.card ≤ (N + 1) / 2 := by
  have hinj : Set.InjOn (fun x : Fin N => (x : ℕ) / 2) ↑T := by
    intro x hx y hy hxy
    by_contra hne
    have hadj := hT hx hy hne
    rw [compl_adj, parityGraph_adj, not_not] at hadj
    have hd : (x : ℕ) / 2 = (y : ℕ) / 2 := hxy
    have hm : (x : ℕ) % 2 = (y : ℕ) % 2 := hadj.2
    exact hne (Fin.ext (by omega))
  have hmaps : ∀ x ∈ T, (x : ℕ) / 2 ∈ Finset.range ((N + 1) / 2) := by
    intro x _
    have := x.isLt
    exact Finset.mem_range.mpr (by omega)
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- No `N ≤ 2k-2` forces, so every `N` that forces satisfies `2k-1 ≤ N`. -/
theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) : 2 * k - 1 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  by_contra hcon
  rcases h (parityGraph N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact parityGraph_cliqueFree_three N S hS
  · have hcard := parityGraph_compl_card hT.isClique
    rw [hT.card_eq] at hcard
    omega

theorem valid : LowerBoundHolds f record :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

end SqueezeBench.Ramsey3.Lower.V000
