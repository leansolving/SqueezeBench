import SqueezeBench.Core
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V008.Def

/-!
# Challenge — HypercubeC4, lower direction, V009

The trusted statement of record for version V009. `record` is the definition hole
`Records/Lower/V009/Def.lean` fills; the three obligations are stated against `SqueezeBench.HypercubeC4.f`,
`nMin` and the previous record `SqueezeBench.HypercubeC4.Lower.V008.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V008 was accepted; never edited.
-/

namespace SqueezeBench.HypercubeC4.Lower.V009

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V008.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V008.record record := sorry

end SqueezeBench.HypercubeC4.Lower.V009
