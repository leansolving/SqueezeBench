import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V001.Def

/-! Record V002 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V002

-- The triangles through a vertex `v` use two distinct neighbours each, and no neighbour twice,
-- so there are at most `⌊deg v / 2⌋ ≤ ⌊(n-1)/2⌋` of them. Summed over the `n` vertices, each
-- triangle counted three times: `T ≤ ⌊n · ⌊(n-1)/2⌋ / 3⌋`.
def record : SqueezeBench.BoundFn := fun n => n * ((n - 1) / 2) / 3

end SqueezeBench.RuzsaSzemeredi.Upper.V002
