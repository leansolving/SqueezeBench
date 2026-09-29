import SqueezeBench.Problems.CapSet.Records.Upper.V000.Def

/-! Record V001 for CapSet, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V001

/-- `(3 ^ n + 1) / 2`, the closed form of the recurrence `u (n+1) = 3 ^ n + u n` from `u 1 = 2`.
The numerator is odd, so the division is exact. -/
def record : SqueezeBench.BoundFn := fun n => (3 ^ n + 1) / 2

end SqueezeBench.CapSet.Upper.V001
