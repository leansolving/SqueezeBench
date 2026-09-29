import SqueezeBench.Problems.CapSet.Records.Upper.V005.Def

/-! Record V006 for CapSet, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V006

/-- `3 ^ (n - 1)` from `n = 3` on: the exact value `f 3 = 9` carried by the multiplicative
slice recursion `f (n+1) ≤ 3 * f n`; below that the exact values `1, 2, 4`. -/
def record : SqueezeBench.BoundFn :=
  fun n => if n < 2 then (3 ^ n + 1) / 2 else if n < 3 then 4 else 3 ^ (n - 1)

end SqueezeBench.CapSet.Upper.V006
