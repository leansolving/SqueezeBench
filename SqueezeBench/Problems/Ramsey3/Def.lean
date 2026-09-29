import Mathlib
import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey.Def
import SqueezeBench.Problems.Ramsey.Finite

/-!
# Off-diagonal Ramsey numbers `R(3, k)`

`f k` is the least `N` such that every 2-colouring of the edges of `K_N` contains a triangle in
the first colour or a `K_k` in the second. See OEIS A000791.

The forcing relation is `SqueezeBench.Ramsey.Forces`, which is already stated with separate clique sizes
`s` and `t` for the two colours — it had to be, because the Erdős–Szekeres induction needs that
form. Fixing `s = 3` and letting `t = k` vary is exactly this problem, so the relation is reused
rather than restated, and with it the whole development in `Ramsey/Finite.lean`.

Consequently there is no `Finite.lean` here: `Ramsey.forces_exists 3 k` *is* the statement that
the set defining `f` is nonempty, so `wellPosed` is a one-liner and stays in this file.
-/

namespace SqueezeBench.Ramsey3

/-- Smallest meaningful parameter value. Below it the conditions degenerate: `Forces N 3 0`
holds for every `N`, since the empty set is a clique of size `0`, and `Forces N 3 1` holds for
every `N ≥ 1`. -/
def nMin : ℕ := 2

@[simp] theorem nMin_eq : nMin = 2 := rfl

/-- The set of `N` that force a triangle or a `K_k` is nonempty. -/
def WellPosed (k : ℕ) : Prop := {N | Ramsey.Forces N 3 k}.Nonempty

/-- `R(3, k)`, pinned to `0` below `nMin`. -/
noncomputable def f (k : ℕ) : ℕ := if k < nMin then 0 else sInf {N | Ramsey.Forces N 3 k}

/-- Well-posedness, immediate from the finite Ramsey theorem. -/
theorem wellPosed (k : ℕ) : WellPosed k := Ramsey.forces_exists 3 k

/-- Upper bounds reduce to exhibiting an `N` that forces. This needs no nonemptiness: a member
is exactly what `Nat.sInf_le` asks for. -/
theorem f_le_of_forces {k N : ℕ} (hk : nMin ≤ k) (hN : Ramsey.Forces N 3 k) : f k ≤ N := by
  rw [f, if_neg (Nat.not_lt.mpr hk)]
  exact Nat.sInf_le hN

/-- Lower bounds reduce to a lower bound on every `N` that forces. -/
theorem le_f {k a : ℕ} (hk : nMin ≤ k) (h : ∀ N, Ramsey.Forces N 3 k → a ≤ N) : a ≤ f k := by
  rw [f, if_neg (Nat.not_lt.mpr hk)]
  exact h _ (Nat.sInf_mem (wellPosed k))

/-- Erdős–Szekeres at `s = 3`: `C(k+1, 2)` vertices force a triangle or a `K_k`.

`Ramsey.forcesOn_choose s t` reads `ForcesOn (C(s+t, s)) (s+1) (t+1)`; at `s = 2` and `t = k-1`
the count is `C(k+1, 2)`. Writing `k` as `m + 1` keeps natural subtraction out of the proof. -/
theorem forces_choose_three {k : ℕ} (hk : 1 ≤ k) :
    Ramsey.Forces (Nat.choose (k + 1) 2) 3 k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : Ramsey.ForcesOn (Nat.choose (m + 1 + 1) 2) 3 (m + 1) := by
    -- The type must be ascribed: `ForcesOn` binds `{V} [Fintype V] [DecidableEq V]`, so an
    -- unascribed `have` instantiates them into metavariables and typeclass search gets stuck.
    have h0 : Ramsey.ForcesOn (Nat.choose (2 + m) 2) 3 (m + 1) := Ramsey.forcesOn_choose 2 m
    rwa [show (2 : ℕ) + m = m + 1 + 1 from by omega] at h0
  exact Ramsey.forces_of_forcesOn h

end SqueezeBench.Ramsey3
