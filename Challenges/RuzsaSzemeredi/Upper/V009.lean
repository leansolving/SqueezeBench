import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V008.Def

/-!
# Challenge — RuzsaSzemeredi, upper direction, V009

The trusted statement of record for version V009. `record` is the definition hole
`Records/Upper/V009/Def.lean` fills; the three obligations are stated against `SqueezeBench.RuzsaSzemeredi.f`,
`nMin` and the previous record `SqueezeBench.RuzsaSzemeredi.Upper.V008.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V008 was accepted; never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V009

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V008.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V008.record record := sorry

end SqueezeBench.RuzsaSzemeredi.Upper.V009
