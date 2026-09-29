import SqueezeBench.Problems.ExGirthFive.Records.Upper.V001.Def

/-! Record V002 for ExGirthFive, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Upper.V002

-- The degree count `∑ d(w)² ≤ n² - n` read off against the chord of `x ↦ x²` through
-- `(q, q²)` and `(q+1, (q+1)²)`: `(2q+1)·2m ≤ n·(n-1+q²+q)`, valid for every `q`.
def bnd (n q : ℕ) : ℕ := n * (n - 1 + q * q + q) / (2 * (2 * q + 1))

-- The best of the three `q` nearest `√(n-1)`; they already attain the minimum over all `q`.
def v : SqueezeBench.BoundFn := fun n =>
  min (bnd n (Nat.sqrt (n - 1) - 1))
    (min (bnd n (Nat.sqrt (n - 1))) (bnd n (Nat.sqrt (n - 1) + 1)))

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExGirthFive.Upper.V001.record v

end SqueezeBench.ExGirthFive.Upper.V002
