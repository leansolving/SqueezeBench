import SqueezeBench.Problems.CapSet.Records.Upper.V003.Def

/-! Record V004 for CapSet, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V004

/-- `2 * 3 ^ n / 5` from `n = 3` on, the fixed point of the sharpened slice recursion;
below that the exact values `1, 2, 4`. -/
def record : SqueezeBench.BoundFn :=
  fun n => if n < 2 then (3 ^ n + 1) / 2 else if n < 3 then 4 else 2 * 3 ^ n / 5

end SqueezeBench.CapSet.Upper.V004
