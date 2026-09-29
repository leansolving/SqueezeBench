import SqueezeBench.Core
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V006.Def

/-!
# Challenge — ExGirthFive, lower direction, V007

The trusted statement of record for version V007. `record` is the definition hole
`Records/Lower/V007/Def.lean` fills; the three obligations are stated against `SqueezeBench.ExGirthFive.f`,
`nMin` and the previous record `SqueezeBench.ExGirthFive.Lower.V006.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V006 was accepted; never edited.
-/

namespace SqueezeBench.ExGirthFive.Lower.V007

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V006.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Lower.V006.record record := sorry

end SqueezeBench.ExGirthFive.Lower.V007
