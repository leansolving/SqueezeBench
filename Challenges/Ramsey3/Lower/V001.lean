import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey3.Records.Lower.V000.Def

/-!
# Challenge — Ramsey3, lower direction, V001

The trusted statement of record for version V001. `record` is the definition hole
`Records/Lower/V001/Def.lean` fills; the three obligations are stated against `SqueezeBench.Ramsey3.f`,
`nMin` and the previous record `SqueezeBench.Ramsey3.Lower.V000.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V000 was accepted; never edited.
-/

namespace SqueezeBench.Ramsey3.Lower.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V000.record record := sorry

end SqueezeBench.Ramsey3.Lower.V001
