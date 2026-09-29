import SqueezeBench.Core
import SqueezeBench.Problems.ExC4.Records.Lower.V005.Def

/-!
# Challenge — ExC4, lower direction, V006

The trusted statement of record for version V006. `record` is the definition hole
`Records/Lower/V006/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExC4.f`,
`nMin` and the previous record `SqueezeBench.ExC4.Lower.V005.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V005 was accepted; never edited.
-/

namespace SqueezeBench.ExC4.Lower.V006

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V005.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V005.record record := sorry

end SqueezeBench.ExC4.Lower.V006
