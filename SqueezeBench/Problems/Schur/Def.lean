import Mathlib
import SqueezeBench.Core

/-!
# Schur numbers `S(k)`

`f k` is the largest `N` such that `{1, …, N}` can be partitioned into `k` sum-free
parts — equivalently, one below the least `N` that forces a monochromatic solution to
`x + y = z` under every `k`-colouring. Known: `1, 4, 13, 44, 160` for `k = 1, …, 5`
(`S(5) = 160` is Heule 2017, DRAT-verified). `S(6)` is unknown, with `536 ≤ S(6) ≤ 1836`.

Sum-free forbids `x + y = z` within a part **including** `x = y`, so `2x = z` is also
forbidden. That is what distinguishes these from the *weak* Schur numbers (OEIS A072842),
which forbid only solutions with `x ≠ y`.

Two conventions appear in the literature and differ by one:

* OEIS **A045652**, used here, is the largest partitionable `N`: `S(4) = 44`.
* OEIS **A030126** is the least forcing `N`, and equals `A045652 + 1`. It is exactly
  `sInf {N | Forces k N}` below, before the `- 1`.
-/

namespace SqueezeBench.Schur

open Finset

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- Every `k`-colouring of `{1, …, N}` has a monochromatic solution to `x + y = z`.
`x = y` is permitted. -/
def Forces (k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin k, ∃ x ∈ Icc 1 N, ∃ y ∈ Icc 1 N, ∃ z ∈ Icc 1 N,
    x + y = z ∧ c x = c y ∧ c y = c z

/-- The set of `N` that force is nonempty — Schur's theorem. Not yet proved here; `f` is
an `sInf` over this set, so bounds on `f` are stated relative to it. -/
def WellPosed (k : ℕ) : Prop := {N | Forces k N}.Nonempty

/-- The Schur number, pinned to `0` below `nMin`. -/
noncomputable def f (k : ℕ) : ℕ :=
  if k < nMin then 0 else sInf {N | Forces k N} - 1

/-- Exhibiting an `N` that forces bounds `f` above by `N - 1`. -/
theorem f_le_of_forces {k N : ℕ} (hk : nMin ≤ k) (hN : Forces k N) : f k ≤ N - 1 := by
  rw [f, if_neg (Nat.not_lt.mpr hk)]
  exact Nat.sub_le_sub_right (Nat.sInf_le hN) 1

/-- Given well-posedness, a lower bound on `f` follows from a lower bound on every `N`
that forces. -/
theorem le_f_of_wellPosed {k a : ℕ} (hk : nMin ≤ k) (hw : WellPosed k)
    (h : ∀ N, Forces k N → a + 1 ≤ N) : a ≤ f k := by
  rw [f, if_neg (Nat.not_lt.mpr hk)]
  have := h _ (Nat.sInf_mem hw)
  omega

end SqueezeBench.Schur
