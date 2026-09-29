import SqueezeBench.Problems.ExGirthFive.Records.Upper.V003.Def

/-! Record V004 for ExGirthFive, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Upper/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Upper.V004

-- Either every degree is at most `q`, and `2m ≤ n·q`, or some vertex has degree at least
-- `q + 1`; its `q + 1` or more neighbours have degrees summing to at most `n - 1`, so their
-- total shortfall below `q` is at least `q(q+1) - (n-1)`, and the chord sum gains `2` per unit
-- of shortfall.
def bnd (n q : ℕ) : ℕ :=
  max (n * q / 2)
    ((n * (n - 1) + n * (q * (q + 1)) + 2 * (n - 1) - 2 * (q * (q + 1))) / (2 * (2 * q + 1)))

-- The best of the three `q` nearest `√(n-1)`, as in V002 and V003.
def v : SqueezeBench.BoundFn := fun n =>
  min (bnd n (Nat.sqrt (n - 1) - 1))
    (min (bnd n (Nat.sqrt (n - 1))) (bnd n (Nat.sqrt (n - 1) + 1)))

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.ExGirthFive.Upper.V003.record v

end SqueezeBench.ExGirthFive.Upper.V004
