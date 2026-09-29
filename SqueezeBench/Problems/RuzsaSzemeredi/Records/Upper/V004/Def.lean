import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V003.Def

/-! Record V004 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V004

-- Every degree of a locally linear graph is even, so along an edge `deg u + deg v` is even and
-- at most `2⌊(n+1)/2⌋`, which is `n` for even `n`. The maximum-degree count of V003 then gives
-- `12 · T ≤ n · 2⌊(n+1)/2⌋`: unchanged for odd `n`, and `⌊n²/12⌋` for even `n`.
def record : SqueezeBench.BoundFn := fun n => n * (2 * ((n + 1) / 2)) / 12

end SqueezeBench.RuzsaSzemeredi.Upper.V004
