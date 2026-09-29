import SqueezeBench.Problems.CapSet.Records.Upper.V004.Def

/-! Record V005 for CapSet, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V005

/-- `10 * 3 ^ (n - 3)` from `n = 3` on: the base value `f 3 ≤ 10` of V004 carried by the
multiplicative slice recursion `f (n+1) ≤ 3 * f n`; below that the exact values `1, 2, 4`. -/
def record : SqueezeBench.BoundFn :=
  fun n => if n < 2 then (3 ^ n + 1) / 2 else if n < 3 then 4 else 10 * 3 ^ (n - 3)

end SqueezeBench.CapSet.Upper.V005
