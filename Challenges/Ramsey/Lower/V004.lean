import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey.Records.Lower.V003.Def

/-!
# Challenge — Ramsey, lower direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Lower/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.Ramsey.f`,
`nMin` and the previous record `SqueezeBench.Ramsey.Lower.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.Ramsey.Lower.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V003.record record := sorry

end SqueezeBench.Ramsey.Lower.V004
