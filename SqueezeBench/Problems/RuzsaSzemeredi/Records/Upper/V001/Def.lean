import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V000.Def

/-! Record V001 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V001

-- In a locally linear graph the triangles are edge-disjoint, so they use `3 * T` of the
-- `C(n, 2)` available edges: `T ≤ C(n, 2) / 3`.
def record : SqueezeBench.BoundFn := fun n => n.choose 2 / 3

end SqueezeBench.RuzsaSzemeredi.Upper.V001
