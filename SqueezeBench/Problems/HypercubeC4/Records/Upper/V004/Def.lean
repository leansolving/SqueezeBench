import SqueezeBench.Problems.HypercubeC4.Records.Upper.V003.Def

/-! Record V004 for HypercubeC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V004

-- One Newton step for the integer square root of `a`; it never falls below `⌊√a⌋`.
def step (a g : ℕ) : ℕ := (g + a / g) / 2

-- Newton's iteration from above, with fuel, stopping as soon as it no longer decreases.
def iter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | k + 1, a, g => if step a g < g then iter k a (step a g) else g

-- An upper bound for `⌊√a⌋`, equal to it once the fuel suffices.
def isqrt (fuel a : ℕ) : ℕ := iter fuel a a

-- The Kővári–Sós–Turán bound inside the cube: `2ⁿ⁻² + √(2²ⁿ⁻⁴ · (1 + 2n(n−1)))`.
def v : SqueezeBench.BoundFn := fun n =>
  2 ^ (n - 2) + isqrt (2 * n + 16) (2 ^ (n - 2) * 2 ^ (n - 2) * (1 + 2 * n * (n - 1)))

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.HypercubeC4.Upper.V003.record v

end SqueezeBench.HypercubeC4.Upper.V004
