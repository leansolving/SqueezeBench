import SqueezeBench.Core
import SqueezeBench.Problems.ExC4.Records.Lower.V004.Def

/-!
# Challenge — ExC4, lower direction, V005

The trusted statement of record for version V005. `record` is the definition hole
`Records/Lower/V005/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExC4.f`,
`nMin` and the previous record `SqueezeBench.ExC4.Lower.V004.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V004 was accepted; never edited.
-/

namespace SqueezeBench.ExC4.Lower.V005

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V004.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V004.record record := sorry

end SqueezeBench.ExC4.Lower.V005
