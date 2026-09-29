import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V000.Def

/-!
# Challenge — RuzsaSzemeredi, upper direction, V001

The trusted statement of record for version V001. `record` is the definition hole
`Records/Upper/V001/Def.lean` fills; the three obligations are stated against `SqueezeBench.RuzsaSzemeredi.f`,
`nMin` and the previous record `SqueezeBench.RuzsaSzemeredi.Upper.V000.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V000 was accepted; never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V000.record record := sorry

end SqueezeBench.RuzsaSzemeredi.Upper.V001
