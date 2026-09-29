import Mathlib

/-!
# Bound functions and the submission obligations

A bound function is just `ℕ → ℕ`. A submission proposes a new record and must discharge
three obligations against the current one: validity, non-regression, and strict
improvement at one point.

Validity is total: each problem pins `f n = 0` below its `nMin`, so `nMin` is needed only
to rule out vacuous witnesses.
-/

namespace SqueezeBench

/-- A candidate lower or upper bound for a problem's `f`. -/
abbrev BoundFn := ℕ → ℕ

/-- `l n ≤ f n` everywhere. -/
def LowerBoundHolds (f l : BoundFn) : Prop := ∀ n, l n ≤ f n

/-- `f n ≤ u n` everywhere. -/
def UpperBoundHolds (f u : BoundFn) : Prop := ∀ n, f n ≤ u n

/-- `l'` is at least as large as the lower-bound record `l` everywhere. -/
def ImprovesLower (l l' : BoundFn) : Prop := ∀ n, l n ≤ l' n

/-- `u'` is at least as small as the upper-bound record `u` everywhere. -/
def ImprovesUpper (u u' : BoundFn) : Prop := ∀ n, u' n ≤ u n

/-- `l'` beats `l` at some `n₀ ≥ nMin`. This is what earns admission. -/
def StrictlyImprovesLower (nMin : ℕ) (l l' : BoundFn) : Prop := ∃ n₀ ≥ nMin, l n₀ < l' n₀

/-- `u'` beats `u` at some `n₀ ≥ nMin`. -/
def StrictlyImprovesUpper (nMin : ℕ) (u u' : BoundFn) : Prop := ∃ n₀ ≥ nMin, u' n₀ < u n₀

namespace ImprovesLower

@[refl] theorem refl (l : BoundFn) : ImprovesLower l l := fun _ => le_refl _

theorem trans {a b c : BoundFn} (h₁ : ImprovesLower a b) (h₂ : ImprovesLower b c) :
    ImprovesLower a c := fun n => le_trans (h₁ n) (h₂ n)

/-- A valid bound above `l` keeps `l` valid. -/
theorem lowerBoundHolds_of {f l l' : BoundFn}
    (h : ImprovesLower l l') (hl' : LowerBoundHolds f l') : LowerBoundHolds f l :=
  fun n => le_trans (h n) (hl' n)

end ImprovesLower

namespace ImprovesUpper

@[refl] theorem refl (u : BoundFn) : ImprovesUpper u u := fun _ => le_refl _

theorem trans {a b c : BoundFn} (h₁ : ImprovesUpper a b) (h₂ : ImprovesUpper b c) :
    ImprovesUpper a c := fun n => le_trans (h₂ n) (h₁ n)

/-- A valid bound below `u` keeps `u` valid. -/
theorem upperBoundHolds_of {f u u' : BoundFn}
    (h : ImprovesUpper u u') (hu' : UpperBoundHolds f u') : UpperBoundHolds f u :=
  fun n => le_trans (hu' n) (h n)

end ImprovesUpper

end SqueezeBench
