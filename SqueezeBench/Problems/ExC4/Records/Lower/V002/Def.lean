import SqueezeBench.Problems.ExC4.Records.Lower.V001.Def

/-! Record V002 for ExC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V002

-- The friendship graph on `n` vertices: `⌊(n-1)/2⌋` triangles glued at one vertex, plus a
-- pendant edge when `n` is even. It is `C₄`-free and has `(n-1) + ⌊(n-1)/2⌋ = ⌊3(n-1)/2⌋` edges.
def record : SqueezeBench.BoundFn := fun n => (n - 1) + (n - 1) / 2

end SqueezeBench.ExC4.Lower.V002
