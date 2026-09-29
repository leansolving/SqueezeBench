import SqueezeBench.Core
import SqueezeBench.Problems.CapSet.Records.Upper.V001.Def

/-!
# Challenge — CapSet, upper direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Upper/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.CapSet.f`,
`nMin` and the previous record `SqueezeBench.CapSet.Upper.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.CapSet.Upper.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Upper.V001.record record := sorry

end SqueezeBench.CapSet.Upper.V002
