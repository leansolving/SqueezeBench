import SqueezeBench.Core
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V001.Def

/-!
# Challenge — HypercubeC4, lower direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Lower/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.HypercubeC4.f`,
`nMin` and the previous record `SqueezeBench.HypercubeC4.Lower.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.HypercubeC4.Lower.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V001.record record := sorry

end SqueezeBench.HypercubeC4.Lower.V002
