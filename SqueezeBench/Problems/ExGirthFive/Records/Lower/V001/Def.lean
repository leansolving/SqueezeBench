import SqueezeBench.Problems.ExGirthFive.Records.Lower.V000.Def

/-! Record V001 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V001

-- The star on `n` vertices has girth `⊤` (it is a tree) and `n - 1` edges; at `n = 0` this is `0`.
def record : SqueezeBench.BoundFn := fun n => n - 1

end SqueezeBench.ExGirthFive.Lower.V001
