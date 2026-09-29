import SqueezeBench.Problems.Roth.Records.Upper.V000.Def

/-! Record V001 for Roth, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V001

-- `2 * ⌈n / 3⌉`: every block of three consecutive integers is itself a 3-AP, so a 3-AP-free
-- set meets it in at most two points.
def v : SqueezeBench.BoundFn := fun n => 2 * ((n + 2) / 3)

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Roth.Upper.V000.record v

end SqueezeBench.Roth.Upper.V001
