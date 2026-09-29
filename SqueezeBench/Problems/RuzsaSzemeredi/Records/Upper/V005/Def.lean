import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V004.Def

/-! Record V005 for RuzsaSzemeredi, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V005

-- The three neighbourhoods of a triangle pairwise meet in one vertex and have empty common
-- intersection, so `deg u + deg v + deg w ≤ n + 3` along every triangle. Summing over the
-- triangles and applying Cauchy-Schwarz to the triangle counts `t_v = deg v / 2` gives
-- `18 · T ≤ n(n+3)`, i.e. `n²/18` instead of the `n²/12` of V003 and V004.
def record : SqueezeBench.BoundFn := fun n => n * (n + 3) / 18

end SqueezeBench.RuzsaSzemeredi.Upper.V005
