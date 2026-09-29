import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V002.Def

/-! Record V003 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V003

-- Two adjacent vertices of a locally linear graph have exactly one common neighbour, so their
-- degrees add up to at most `n + 1`. Taking a vertex `v` of maximum degree `d`, its `d`
-- neighbours have degree at most `n + 1 - d` and the other `n - d` vertices at most `d`, so
-- `2 · #edges ≤ d · (2n + 1 - 2d) ≤ n(n+1)/2`. With `#edges = 3 · T` this is `T ≤ n(n+1)/12`.
def record : SqueezeBench.BoundFn := fun n => n * (n + 1) / 12

end SqueezeBench.RuzsaSzemeredi.Upper.V003
