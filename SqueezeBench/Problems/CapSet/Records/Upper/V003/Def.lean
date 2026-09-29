import SqueezeBench.Problems.CapSet.Records.Upper.V002.Def

/-! Record V003 for CapSet, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V003

/-- `f 2 = 4` carried up by `f (n+1) ≤ 3 * f n`: `4 * 3 ^ (n - 2)` from `n = 2` on. -/
def record : SqueezeBench.BoundFn :=
  fun n => if n < 2 then (3 ^ n + 1) / 2 else 4 * 3 ^ (n - 2)

end SqueezeBench.CapSet.Upper.V003
