import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V001.Def

/-!
# Challenge — RuzsaSzemeredi, upper direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Upper/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.RuzsaSzemeredi.f`,
`nMin` and the previous record `SqueezeBench.RuzsaSzemeredi.Upper.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V001.record record := sorry

end SqueezeBench.RuzsaSzemeredi.Upper.V002
