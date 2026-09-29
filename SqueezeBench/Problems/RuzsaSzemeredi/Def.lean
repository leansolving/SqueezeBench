import Mathlib
import SqueezeBench.Core

/-!
# The Ruzsa–Szemerédi number

`f n` is the largest number of **triangles** in a locally linear graph on `n` vertices — a graph
in which every edge lies in exactly one triangle.

`f` reuses Mathlib's `ruzsaSzemerediNumberNat`, a `Nat.findGreatest` over a `Fintype`, so `f` is
total and needs no nonemptiness lemma.

**A trap worth stating, because the names mislead.** Mathlib's docstrings for
`ruzsaSzemerediNumber` say "the maximum number of *edges* a locally linear graph can have", but
the definition is `Nat.findGreatest (fun m ↦ ∃ G, #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) …`
— it counts **triangles**. The companion bound `ruzsaSzemerediNumberNat_le : ≤ n.choose 3`
confirms this: an edge count would be bounded by `n.choose 2`. Since a locally linear graph has
`#edges = 3 · #triangles`, reading the docstring instead of the body gives a quantity three
times too large. `f` here is the triangle count, matching the definition.

`f` is `noncomputable`, and the predicate existentially quantifies a `DecidableRel` instance, so
it is not decidable either. Small values therefore cannot be checked by `decide`; lower bounds
come from exhibiting a graph.
-/

namespace SqueezeBench.RuzsaSzemeredi

open SimpleGraph

/-- Smallest meaningful parameter value. Below three vertices there is no triangle. -/
def nMin : ℕ := 3

@[simp] theorem nMin_eq : nMin = 3 := rfl

/-- The Ruzsa–Szemerédi number, pinned to `0` below `nMin`. -/
noncomputable def f (n : ℕ) : ℕ := if n < nMin then 0 else ruzsaSzemerediNumberNat n

theorem f_of_le {n : ℕ} (hn : nMin ≤ n) : f n = ruzsaSzemerediNumberNat n := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]

/-- Lower bounds reduce to exhibiting a locally linear graph and counting its triangles. -/
theorem le_f_of_locallyLinear {n : ℕ} (hn : nMin ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.LocallyLinear) : (G.cliqueFinset 3).card ≤ f n := by
  rw [f_of_le hn]
  exact hG.le_ruzsaSzemerediNumber

/-- The ambient bound `C(n, 3)`: there are only that many triples to be triangles. -/
theorem f_le_choose_three (n : ℕ) : f n ≤ n.choose 3 := by
  rw [f]
  split
  · exact Nat.zero_le _
  · exact ruzsaSzemerediNumberNat_le

/-- Monotonicity, inherited from `ruzsaSzemerediNumberNat`. -/
theorem f_mono {m n : ℕ} (hm : nMin ≤ m) (h : m ≤ n) : f m ≤ f n := by
  rw [f_of_le hm, f_of_le (le_trans hm h)]
  exact ruzsaSzemerediNumberNat_mono h

/-- A single triangle is locally linear, so `f n ≥ 1` as soon as there are three vertices.
Everything about `K₃` is concrete, so `decide` settles both facts about it. -/
theorem one_le_f {n : ℕ} (hn : nMin ≤ n) : 1 ≤ f n := by
  have hll : (⊤ : SimpleGraph (Fin 3)).LocallyLinear := by decide
  have hcard : ((⊤ : SimpleGraph (Fin 3)).cliqueFinset 3).card = 1 := by decide
  have h3 : 1 ≤ f 3 := by
    have := le_f_of_locallyLinear (n := 3) (by simp) ⊤ hll
    omega
  have hm := f_mono (show nMin ≤ 3 by simp) hn
  omega

end SqueezeBench.RuzsaSzemeredi
