import SqueezeBench.Core
import SqueezeBench.Problems.CapSet.Records.Upper.V004.Def

/-!
# Challenge — CapSet, upper direction, V005

The trusted statement of record for version V005. `record` is the definition hole
`Records/Upper/V005/Def.lean` fills; the three obligations are stated against `SqueezeBench.CapSet.f`,
`nMin` and the previous record `SqueezeBench.CapSet.Upper.V004.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V004 was accepted; never edited.
-/

namespace SqueezeBench.CapSet.Upper.V005

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V004.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Upper.V004.record record := sorry

end SqueezeBench.CapSet.Upper.V005
