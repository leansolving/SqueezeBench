import SqueezeBench.Problems.ExGirthFive.Records.Upper.V002.Def

/-! Record V003 for ExGirthFive, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Upper.V003

-- The largest degree a minimum-degree vertex can have once some vertex has degree `q + 1`:
-- the neighbours of that vertex all have degree at least the minimum, and their degrees sum to
-- at most `n - 1`.
def lo (n q : ℕ) : ℕ := min ((n - 1) / (q + 1)) q

-- Either every degree is at most `q`, and `2m ≤ n·q`, or a minimum-degree vertex of degree at
-- most `lo n q` is taken out of the chord sum, which gains against V002's `n·q(q+1)`.
def bnd (n q : ℕ) : ℕ :=
  max (n * q / 2)
    ((lo n q * (2 * q + 1 - lo n q) + n * (n - 1) + (n - 1) * (q * (q + 1))) /
      (2 * (2 * q + 1)))

-- The best of the three `q` nearest `√(n-1)`, as in V002.
def v : SqueezeBench.BoundFn := fun n =>
  min (bnd n (Nat.sqrt (n - 1) - 1))
    (min (bnd n (Nat.sqrt (n - 1))) (bnd n (Nat.sqrt (n - 1) + 1)))

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.ExGirthFive.Upper.V002.record v

end SqueezeBench.ExGirthFive.Upper.V003
