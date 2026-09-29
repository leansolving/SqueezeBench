import SqueezeBench.Core
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V007.Def

/-!
# Challenge — HypercubeC4, upper direction, V008

The trusted statement of record for version V008. `record` is the definition hole
`Records/Upper/V008/Def.lean` fills; the three obligations are stated against `SqueezeBench.HypercubeC4.f`,
`nMin` and the previous record `SqueezeBench.HypercubeC4.Upper.V007.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V007 was accepted; never edited.
-/

namespace SqueezeBench.HypercubeC4.Upper.V008

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V007.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V007.record record := sorry

end SqueezeBench.HypercubeC4.Upper.V008
