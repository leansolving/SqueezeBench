import SqueezeBench.Core
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V001.Def

/-!
# Challenge — ExGirthFive, upper direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Upper/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExGirthFive.f`,
`nMin` and the previous record `SqueezeBench.ExGirthFive.Upper.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.ExGirthFive.Upper.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V001.record record := sorry

end SqueezeBench.ExGirthFive.Upper.V002
