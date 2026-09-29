import SqueezeBench.Problems.ExC4.Records.Lower.V000.Def

/-! Record V001 for ExC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V001

-- The star on `n` vertices is `C₄`-free and has `n - 1` edges; at `n = 0` this is `0`.
def record : SqueezeBench.BoundFn := fun n => n - 1

end SqueezeBench.ExC4.Lower.V001
