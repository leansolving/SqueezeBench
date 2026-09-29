import SqueezeBench.Core
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V000.Def

/-!
# Challenge — ExGirthFive, lower direction, V001

The trusted statement of record for version V001. `record` is the definition hole
`Records/Lower/V001/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExGirthFive.f`,
`nMin` and the previous record `SqueezeBench.ExGirthFive.Lower.V000.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V000 was accepted; never edited.
-/

namespace SqueezeBench.ExGirthFive.Lower.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Lower.V000.record record := sorry

end SqueezeBench.ExGirthFive.Lower.V001
