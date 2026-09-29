import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V005.Def

/-!
# Challenge — RuzsaSzemeredi, upper direction, V006

The trusted statement of record for version V006. `record` is the definition hole
`Records/Upper/V006/Def.lean` fills; the three obligations are stated against `SqueezeBench.RuzsaSzemeredi.f`,
`nMin` and the previous record `SqueezeBench.RuzsaSzemeredi.Upper.V005.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V005 was accepted; never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V006

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.RuzsaSzemeredi.Upper.V005.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Upper.V005.record record := sorry

end SqueezeBench.RuzsaSzemeredi.Upper.V006
