import SqueezeBench.Problems.Ramsey.Records.Lower.V008.Def

/-! Record V009 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V009.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Ramsey.Lower.V009

def record : SqueezeBench.BoundFn := SqueezeBench.patch SqueezeBench.Ramsey.Lower.V008.record 5 43

end SqueezeBench.Ramsey.Lower.V009
