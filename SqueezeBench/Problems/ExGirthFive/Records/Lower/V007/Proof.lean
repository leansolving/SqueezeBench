import SqueezeBench.Problems.ExGirthFive.Records.Lower.V007.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V006.Proof

/-! Record V007 for ExGirthFive, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V007.lean`. -/

namespace SqueezeBench.ExGirthFive.Lower.V007

open SqueezeBench SqueezeBench.ExGirthFive

-- Every entry of the table is prime, one `norm_num` check each.
theorem primes_prime : ∀ p ∈ primes, Nat.Prime p := by
  intro p hp
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

-- Each entry contributes its affine plane blocks, by the parametric `block_le` of V006.
theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f blocks := by
  intro n
  have h : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) →
      (l.map fun p => p * p * p * (n / (2 * p * p))).foldr max 0 ≤ f n := by
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons c t ih =>
        exact max_le (V006.block_le c n (hl c (by simp))) (ih fun q hq => hl q (by simp [hq]))
  exact h primes primes_prime

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V006.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 8718968605206943442)
    (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V007
