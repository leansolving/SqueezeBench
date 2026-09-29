import SqueezeBench.Problems.ExC4.Records.Upper.V000.Def

/-! Record V001 for ExC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Upper.V001

-- One Newton step for the integer square root, made monotone by `min`.
def sqrtStep (x g : ℕ) : ℕ := min g ((g + x / g) / 2)

-- `k` Newton steps from the initial guess `g`.
def sqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | k + 1, x, g => sqrtIter k x (sqrtStep x g)

-- Kernel-friendly integer square root: 64 Newton steps, never below `Nat.sqrt x`.
def isqrt (x : ℕ) : ℕ := sqrtIter 64 x (x + 1)

-- Reiman's bound `n(1 + √(4n-3))/4`, written as `(n + √(n²(4n-3)))/4`.
def v : SqueezeBench.BoundFn := fun n => (n + isqrt (n * n * (4 * n - 3))) / 4

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExC4.Upper.V000.record v

end SqueezeBench.ExC4.Upper.V001
