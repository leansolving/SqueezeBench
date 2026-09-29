import SqueezeBench.Core.Bound

/-!
# Record construction idioms

Two ways to build a new record from the current one, each with its obligation lemmas
ready to `exact`:

* `patch` — override the record at a point.
* `maxWith` / `minWith` — fold in an unrelated bound. Non-regression is then
  `le_max_left` / `min_le_left`, so this always works.

A submitter may instead write a wholesale closed form and prove `Improves*` by hand.
-/

namespace SqueezeBench

/-! ## Padding below `nMin`

Each problem pins `f n = 0` for `n < nMin`, while `LowerBoundHolds` quantifies over every
`n`. A lower bound must therefore vanish below `nMin` too: `fun n => 2 ^ n` is not a valid
lower record for any problem, because it is `1` at `n = 0` where `f` is `0`. `pin` supplies
the padding, and `pin_lowerBoundHolds` reduces the obligation to the range that matters.

Upper bounds need no such treatment: below `nMin` the goal is `f n ≤ u n` with `f n = 0`,
which holds for any `u`. -/

/-- Pad a bound with `0` below `nMin`. -/
def pin (nMin : ℕ) (l : BoundFn) : BoundFn := fun n => if n < nMin then 0 else l n

@[simp] theorem pin_of_lt {nMin : ℕ} {l : BoundFn} {n : ℕ} (h : n < nMin) :
    pin nMin l n = 0 := by simp [pin, h]

@[simp] theorem pin_of_ge {nMin : ℕ} {l : BoundFn} {n : ℕ} (h : nMin ≤ n) :
    pin nMin l n = l n := by simp [pin, Nat.not_lt.mpr h]

/-- A padded lower bound only has to be proved above `nMin`. -/
theorem pin_lowerBoundHolds {f l : BoundFn} {nMin : ℕ}
    (h : ∀ n, nMin ≤ n → l n ≤ f n) : LowerBoundHolds f (pin nMin l) := by
  intro n
  unfold pin
  split
  · exact Nat.zero_le _
  · exact h n (Nat.not_lt.mp ‹¬ n < nMin›)

/-! ## Point patch -/

/-- Override a bound function at a single point. -/
def patch (l : BoundFn) (n₀ y₀ : ℕ) : BoundFn := fun n => if n = n₀ then y₀ else l n

@[simp] theorem patch_at (l : BoundFn) (n₀ y₀ : ℕ) : patch l n₀ y₀ n₀ = y₀ := by
  simp [patch]

@[simp] theorem patch_of_ne {l : BoundFn} {n₀ : ℕ} (y₀ : ℕ) {n : ℕ} (h : n ≠ n₀) :
    patch l n₀ y₀ n = l n := by
  simp [patch, h]

/-- `hy` is the mathematics; the rest is bookkeeping. -/
theorem patch_valid {f l : BoundFn} {n₀ y₀ : ℕ}
    (hl : LowerBoundHolds f l) (hy : y₀ ≤ f n₀) : LowerBoundHolds f (patch l n₀ y₀) := by
  intro n; unfold patch; split
  · subst ‹n = n₀›; exact hy
  · exact hl n

theorem patch_improves {l : BoundFn} {n₀ y₀ : ℕ} (h : l n₀ ≤ y₀) :
    ImprovesLower l (patch l n₀ y₀) := by
  intro n; unfold patch; split
  · subst ‹n = n₀›; exact h
  · exact le_refl _

theorem patch_strict {nMin : ℕ} {l : BoundFn} {n₀ y₀ : ℕ}
    (hn : n₀ ≥ nMin) (h : l n₀ < y₀) : StrictlyImprovesLower nMin l (patch l n₀ y₀) :=
  ⟨n₀, hn, by simpa [patch] using h⟩

theorem patch_valid' {f u : BoundFn} {n₀ y₀ : ℕ}
    (hu : UpperBoundHolds f u) (hy : f n₀ ≤ y₀) : UpperBoundHolds f (patch u n₀ y₀) := by
  intro n; unfold patch; split
  · subst ‹n = n₀›; exact hy
  · exact hu n

theorem patch_improves' {u : BoundFn} {n₀ y₀ : ℕ} (h : y₀ ≤ u n₀) :
    ImprovesUpper u (patch u n₀ y₀) := by
  intro n; unfold patch; split
  · subst ‹n = n₀›; exact h
  · exact le_refl _

theorem patch_strict' {nMin : ℕ} {u : BoundFn} {n₀ y₀ : ℕ}
    (hn : n₀ ≥ nMin) (h : y₀ < u n₀) : StrictlyImprovesUpper nMin u (patch u n₀ y₀) :=
  ⟨n₀, hn, by simpa [patch] using h⟩

/-! ## Pointwise max / min -/

/-- Fold an unrelated lower bound into the record. -/
def maxWith (l v : BoundFn) : BoundFn := fun n => max (l n) (v n)

/-- Fold an unrelated upper bound into the record. -/
def minWith (u v : BoundFn) : BoundFn := fun n => min (u n) (v n)

@[simp] theorem maxWith_apply (l v : BoundFn) (n : ℕ) :
    maxWith l v n = max (l n) (v n) := rfl

@[simp] theorem minWith_apply (u v : BoundFn) (n : ℕ) :
    minWith u v n = min (u n) (v n) := rfl

theorem maxWith_valid {f l v : BoundFn}
    (hl : LowerBoundHolds f l) (hv : LowerBoundHolds f v) :
    LowerBoundHolds f (maxWith l v) := fun n => max_le (hl n) (hv n)

/-- Unconditional: folding in any bound never regresses. -/
theorem maxWith_improves {l v : BoundFn} : ImprovesLower l (maxWith l v) :=
  fun _ => le_max_left _ _

theorem minWith_valid {f u v : BoundFn}
    (hu : UpperBoundHolds f u) (hv : UpperBoundHolds f v) :
    UpperBoundHolds f (minWith u v) := fun n => le_min (hu n) (hv n)

/-- Unconditional; see `maxWith_improves`. -/
theorem minWith_improves {u v : BoundFn} : ImprovesUpper u (minWith u v) :=
  fun _ => min_le_left _ _

theorem maxWith_strict {nMin : ℕ} {l v : BoundFn} {n₀ : ℕ}
    (hn : n₀ ≥ nMin) (h : l n₀ < v n₀) : StrictlyImprovesLower nMin l (maxWith l v) :=
  ⟨n₀, hn, by simpa [maxWith] using h⟩

theorem minWith_strict {nMin : ℕ} {u v : BoundFn} {n₀ : ℕ}
    (hn : n₀ ≥ nMin) (h : v n₀ < u n₀) : StrictlyImprovesUpper nMin u (minWith u v) :=
  ⟨n₀, hn, by simpa [minWith] using h⟩

end SqueezeBench
