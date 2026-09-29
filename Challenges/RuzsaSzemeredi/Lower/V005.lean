import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V004.Def

/-!
# Challenge — RuzsaSzemeredi, lower direction, V005

The trusted statement of record for version V005. `record` is the definition hole
`Records/Lower/V005/Def.lean` fills; the three obligations are stated against `SqueezeBench.RuzsaSzemeredi.f`,
`nMin` and the previous record `SqueezeBench.RuzsaSzemeredi.Lower.V004.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V004 was accepted; never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V005

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V004.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V004.record record := sorry

end SqueezeBench.RuzsaSzemeredi.Lower.V005
