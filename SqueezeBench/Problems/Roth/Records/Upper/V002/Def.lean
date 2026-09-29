import SqueezeBench.Problems.Roth.Records.Upper.V001.Def

/-! Record V002 for Roth, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V002

-- `⌊(n+3)/2⌋`: a 3-AP-free set and the halved sums of one of its parity classes are disjoint
-- subsets of `{0, …, n-1}`.
def v : SqueezeBench.BoundFn := fun n => (n + 3) / 2

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Roth.Upper.V001.record v

end SqueezeBench.Roth.Upper.V002
