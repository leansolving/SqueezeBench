import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey.Records.Lower.V010.Def

/-!
# Challenge — Ramsey, lower direction, V011

The trusted statement of record for version V011. `record` is the definition hole
`Records/Lower/V011/Def.lean` fills; the three obligations are stated against `SqueezeBench.Ramsey.f`,
`nMin` and the previous record `SqueezeBench.Ramsey.Lower.V010.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V010 was accepted; never edited.
-/

namespace SqueezeBench.Ramsey.Lower.V011

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V010.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V010.record record := sorry

end SqueezeBench.Ramsey.Lower.V011
