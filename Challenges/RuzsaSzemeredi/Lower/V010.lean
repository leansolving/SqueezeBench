import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V009.Def

/-!
# Challenge — RuzsaSzemeredi, lower direction, V010

The trusted statement of record for version V010. `record` is the definition hole
`Records/Lower/V010/Def.lean` fills; the three obligations are stated against `SqueezeBench.RuzsaSzemeredi.f`,
`nMin` and the previous record `SqueezeBench.RuzsaSzemeredi.Lower.V009.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V009 was accepted; never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V010

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V009.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V009.record record := sorry

end SqueezeBench.RuzsaSzemeredi.Lower.V010
