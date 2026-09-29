import SqueezeBench.Core
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V006.Def

/-!
# Challenge — HypercubeC4, lower direction, V007

The trusted statement of record for version V007. `record` is the definition hole
`Records/Lower/V007/Def.lean` fills; the three obligations are stated against `SqueezeBench.HypercubeC4.f`,
`nMin` and the previous record `SqueezeBench.HypercubeC4.Lower.V006.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V006 was accepted; never edited.
-/

namespace SqueezeBench.HypercubeC4.Lower.V007

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V006.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V006.record record := sorry

end SqueezeBench.HypercubeC4.Lower.V007
