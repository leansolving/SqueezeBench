import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V001.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V000.Proof

/-! Record V001 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the three obligations.
Mathlib's `rothNumberNat_le_ruzsaSzemerediNumberNat` is the tripartite construction: it turns a
3-AP-free subset of `[0, m)` of size `r` into a locally linear graph on `6m+3` vertices with
`(2m+1) · r` triangles. `{0, 1}` is 3-AP-free, so `r₃(m) ≥ min m 2`, and monotonicity of `f`
carries the bound from `6m+3` to every larger `n`. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V001

open SqueezeBench

/-- `{0, 1}` contains no nontrivial three-term progression. -/
theorem threeAPFree_zero_one : ThreeAPFree ((({0, 1} : Finset ℕ) : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

/-- A singleton contains no nontrivial three-term progression. -/
theorem threeAPFree_zero : ThreeAPFree ((({0} : Finset ℕ) : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc _
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
  omega

/-- The Roth number of `[0, m)` is at least the size of `{0, 1} ∩ [0, m)`. -/
theorem min_two_le_rothNumberNat (m : ℕ) : min m 2 ≤ rothNumberNat m := by
  match m with
  | 0 => simp
  | 1 =>
      have h1 : 1 ≤ rothNumberNat 1 :=
        ThreeAPFree.le_rothNumberNat ({0} : Finset ℕ) threeAPFree_zero
          (by intro x hx; simp at hx; omega) (by decide)
      simpa using h1
  | (k + 2) =>
      have h2 : 2 ≤ rothNumberNat 2 :=
        ThreeAPFree.le_rothNumberNat ({0, 1} : Finset ℕ) threeAPFree_zero_one
          (by intro x hx; simp at hx; omega) (by decide)
      exact le_trans (by simp) (le_trans h2 (rothNumberNat.monotone (by omega)))

/-- The tripartite construction, transferred to `f`. -/
theorem key (m : ℕ) : (2 * m + 1) * rothNumberNat m ≤ SqueezeBench.RuzsaSzemeredi.f (6 * m + 3) := by
  rw [SqueezeBench.RuzsaSzemeredi.f_of_le (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]; omega)]
  exact rothNumberNat_le_ruzsaSzemerediNumberNat m

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f v := by
  intro n
  by_cases hn : 3 ≤ n
  · have hle : 6 * blocks n + 3 ≤ n := by unfold blocks; omega
    calc v n = (2 * blocks n + 1) * min (blocks n) 2 := rfl
      _ ≤ (2 * blocks n + 1) * rothNumberNat (blocks n) :=
          Nat.mul_le_mul_left _ (min_two_le_rothNumberNat _)
      _ ≤ SqueezeBench.RuzsaSzemeredi.f (6 * blocks n + 3) := key _
      _ ≤ SqueezeBench.RuzsaSzemeredi.f n :=
          SqueezeBench.RuzsaSzemeredi.f_mono
            (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]; omega) hle
  · have h0 : blocks n = 0 := by unfold blocks; omega
    simp [v, h0]

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record :=
  maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V000.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V000.record record :=
  maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 15) (by decide) (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V001
