import SqueezeBench.Core
import SqueezeBench.Problems.CapSet.Records.Lower.V005.Def

/-!
# Challenge — CapSet, lower direction, V006

The trusted statement of record for version V006. `record` is the definition hole
`Records/Lower/V006/Def.lean` fills; the three obligations are stated against `SqueezeBench.CapSet.f`,
`nMin` and the previous record `SqueezeBench.CapSet.Lower.V005.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V005 was accepted; never edited.
-/

namespace SqueezeBench.CapSet.Lower.V006

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.CapSet.Lower.V005.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Lower.V005.record record := sorry

end SqueezeBench.CapSet.Lower.V006
