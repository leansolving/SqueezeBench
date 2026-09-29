import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Record V002 for Tutorial, lower direction, by Pablo Manrique: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Tutorial/Lower/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The patch idiom: `{1, 3, 4, 5}` is doubling-free and lies in `{1, …, 6}`, so `f 6 ≥ 4` where
V001 claimed only `1`. -/

namespace SqueezeBench.Tutorial.Lower.V002

def record : SqueezeBench.BoundFn := SqueezeBench.patch SqueezeBench.Tutorial.Lower.V001.record 6 4

end SqueezeBench.Tutorial.Lower.V002
