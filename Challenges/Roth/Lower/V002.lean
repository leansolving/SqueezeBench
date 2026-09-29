import SqueezeBench.Core
import SqueezeBench.Problems.Roth.Records.Lower.V001.Def

/-!
# Challenge — Roth, lower direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Lower/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.Roth.f`,
`nMin` and the previous record `SqueezeBench.Roth.Lower.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.Roth.Lower.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V001.record record := sorry

end SqueezeBench.Roth.Lower.V002
