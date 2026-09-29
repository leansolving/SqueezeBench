import SqueezeBench.Core
import SqueezeBench.Problems.ExC4.Records.Upper.V003.Def

/-!
# Challenge — ExC4, upper direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Upper/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExC4.f`,
`nMin` and the previous record `SqueezeBench.ExC4.Upper.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.ExC4.Upper.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V003.record record := sorry

end SqueezeBench.ExC4.Upper.V004
