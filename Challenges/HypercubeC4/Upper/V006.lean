import SqueezeBench.Core
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V005.Def

/-!
# Challenge — HypercubeC4, upper direction, V006

The trusted statement of record for version V006. `record` is the definition hole
`Records/Upper/V006/Def.lean` fills; the three obligations are stated against `SqueezeBench.HypercubeC4.f`,
`nMin` and the previous record `SqueezeBench.HypercubeC4.Upper.V005.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V005 was accepted; never edited.
-/

namespace SqueezeBench.HypercubeC4.Upper.V006

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V005.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V005.record record := sorry

end SqueezeBench.HypercubeC4.Upper.V006
