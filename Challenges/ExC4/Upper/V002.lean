import SqueezeBench.Core
import SqueezeBench.Problems.ExC4.Records.Upper.V001.Def

/-!
# Challenge — ExC4, upper direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Upper/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExC4.f`,
`nMin` and the previous record `SqueezeBench.ExC4.Upper.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.ExC4.Upper.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExC4.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExC4.Upper.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Upper.V001.record record := sorry

end SqueezeBench.ExC4.Upper.V002
