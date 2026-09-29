import SqueezeBench.Core
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V002.Def

/-!
# Challenge — ExGirthFive, upper direction, V003

The trusted statement of record for version V003. `record` is the definition hole
`Records/Upper/V003/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExGirthFive.f`,
`nMin` and the previous record `SqueezeBench.ExGirthFive.Upper.V002.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V002 was accepted; never edited.
-/

namespace SqueezeBench.ExGirthFive.Upper.V003

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V002.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V002.record record := sorry

end SqueezeBench.ExGirthFive.Upper.V003
