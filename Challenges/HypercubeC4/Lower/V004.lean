import SqueezeBench.Core
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V003.Def

/-!
# Challenge — HypercubeC4, lower direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Lower/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.HypercubeC4.f`,
`nMin` and the previous record `SqueezeBench.HypercubeC4.Lower.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.HypercubeC4.Lower.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V003.record record := sorry

end SqueezeBench.HypercubeC4.Lower.V004
