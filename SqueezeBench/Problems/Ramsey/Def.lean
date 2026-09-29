import Mathlib
import SqueezeBench.Core

/-!
# Diagonal Ramsey numbers `R(n, n)`

`f n` is the least `N` such that every 2-colouring of the edges of `K_N` contains a
monochromatic `K_n`. Known: `R(1,1) = 1`, `R(2,2) = 2`, `R(3,3) = 6`, `R(4,4) = 18`, and
`43 ≤ R(5,5) ≤ 46`.

A 2-colouring of the edges of `K_N` is the same thing as a graph `G` on `Fin N`: one
colour class is `G`, the other is `Gᶜ`. So `Forces` is phrased in terms of graphs, and a
monochromatic `K_n` is a clique of size `n` in `G` or in `Gᶜ`.

`Forces` is stated **off-diagonal**, with separate sizes `s` and `t` for the two colours,
because that is the form the Erdős–Szekeres induction needs; `f` uses the diagonal case
`s = t = n`. That induction is carried out in `SqueezeBench.Problems.Ramsey.Finite`,
which proves `WellPosed`.
-/

namespace SqueezeBench.Ramsey

/-- Smallest meaningful parameter value. At `n < 2` the clique conditions degenerate. -/
def nMin : ℕ := 2

@[simp] theorem nMin_eq : nMin = 2 := rfl

/-- Every graph on `N` vertices contains a clique of size `s`, or a clique of size `t` in
its complement. Equivalently: every 2-colouring of the edges of `K_N` contains a `K_s` in
the first colour or a `K_t` in the second. -/
def Forces (N s t : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ S : Finset (Fin N), G.IsNClique s S) ∨ (∃ T : Finset (Fin N), Gᶜ.IsNClique t T)

/-- The set of `N` that force the diagonal Ramsey property is nonempty. Proved in
`SqueezeBench.Problems.Ramsey.Finite`. -/
def WellPosed (n : ℕ) : Prop := {N | Forces N n n}.Nonempty

/-- The diagonal Ramsey number, pinned to `0` below `nMin`. -/
noncomputable def f (n : ℕ) : ℕ := if n < nMin then 0 else sInf {N | Forces N n n}

/-- Exhibiting an `N` that forces bounds `f` above by it. -/
theorem f_le_of_forces {n N : ℕ} (hn : nMin ≤ n) (hN : Forces N n n) : f n ≤ N := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  exact Nat.sInf_le hN

/-- Given well-posedness, a lower bound on `f` follows from a lower bound on every `N`
that forces. -/
theorem le_f_of_wellPosed {n a : ℕ} (hn : nMin ≤ n) (hw : WellPosed n)
    (h : ∀ N, Forces N n n → a ≤ N) : a ≤ f n := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  exact h _ (Nat.sInf_mem hw)

end SqueezeBench.Ramsey
