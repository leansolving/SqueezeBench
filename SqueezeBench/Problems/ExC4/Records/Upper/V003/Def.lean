import SqueezeBench.Problems.ExC4.Records.Upper.V002.Def

/-! Record V003 for ExC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Upper.V003

-- The tangent bound at an odd degree level `q`: from `(2q−1)·2m + n ≤ n(n−1) + n·q²`.
def tangentBound (n q : ℕ) : ℕ := (n * (n - 1) + n * (q * q) - n) / (2 * q - 1) / 2

-- The odd degree level closest to the average degree V002 still allows.
def qBase (n : ℕ) : ℕ := 2 * (2 * SqueezeBench.ExC4.Upper.V002.record n / n / 2) + 1

def v : SqueezeBench.BoundFn := fun n =>
  min (tangentBound n (qBase n)) (tangentBound n (qBase n + 2))

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExC4.Upper.V002.record v

end SqueezeBench.ExC4.Upper.V003
