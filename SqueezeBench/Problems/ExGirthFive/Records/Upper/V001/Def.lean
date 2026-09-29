import SqueezeBench.Problems.ExGirthFive.Records.Upper.V000.Def

/-! Record V001 for ExGirthFive, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Upper.V001

-- The Moore-type bound `(n/2)·√(n-1) = √(n²(n-1))/2`, in ℕ arithmetic.
-- `n * (n * n - n)` is `n²(n-1)` written without a subtraction that could underflow.
def v : SqueezeBench.BoundFn := fun n => Nat.sqrt (n * (n * n - n)) / 2

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExGirthFive.Upper.V000.record v

end SqueezeBench.ExGirthFive.Upper.V001
