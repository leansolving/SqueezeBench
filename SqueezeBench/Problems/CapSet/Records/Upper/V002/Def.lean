import SqueezeBench.Problems.CapSet.Records.Upper.V001.Def

/-! Record V002 for CapSet, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V002

/-- `(3 ^ n - 1) / 2` from `n = 2` on: the same recurrence `u (n+1) = 3 ^ n + u n` as V001,
started at the exact value `u 2 = 4` instead of at `u 1 = 2`. Both divisions are exact. -/
def record : SqueezeBench.BoundFn :=
  fun n => if n < 2 then (3 ^ n + 1) / 2 else (3 ^ n - 1) / 2

end SqueezeBench.CapSet.Upper.V002
