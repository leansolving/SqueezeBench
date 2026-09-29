import SqueezeBench.Core
import SqueezeBench.Problems.CapSet.Records.Upper.V008.Def

/-!
# Challenge — CapSet, upper direction, V009

The trusted statement of record for version V009. `record` is the definition hole
`Records/Upper/V009/Def.lean` fills; the three obligations are stated against `SqueezeBench.CapSet.f`,
`nMin` and the previous record `SqueezeBench.CapSet.Upper.V008.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V008 was accepted; never edited.
-/

namespace SqueezeBench.CapSet.Upper.V009

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V008.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Upper.V008.record record := sorry

end SqueezeBench.CapSet.Upper.V009
