import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V005.Def

/-! Record V006 for RuzsaSzemeredi, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V006

-- Every degree of a locally linear graph is even, so the three degrees of a triangle add up to
-- an even number; V005's bound `deg u + deg v + deg w ≤ n + 3` therefore sharpens to `≤ n + 2`
-- when `n` is even, and V005's count then gives `18 · T ≤ n(n+2)` for even `n`.
-- For odd `n` the record is V005's `⌊n(n+3)/18⌋`.
def record : SqueezeBench.BoundFn := fun n => n * (n + 2 + n % 2) / 18

end SqueezeBench.RuzsaSzemeredi.Upper.V006
