import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey3.Records.Lower.V003.Def

/-!
# Challenge — Ramsey3, lower direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Lower/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.Ramsey3.f`,
`nMin` and the previous record `SqueezeBench.Ramsey3.Lower.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.Ramsey3.Lower.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V003.record record := sorry

end SqueezeBench.Ramsey3.Lower.V004
