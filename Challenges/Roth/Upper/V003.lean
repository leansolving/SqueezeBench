import SqueezeBench.Core
import SqueezeBench.Problems.Roth.Records.Upper.V002.Def

/-!
# Challenge — Roth, upper direction, V003

The trusted statement of record for version V003. `record` is the definition hole
`Records/Upper/V003/Def.lean` fills; the three obligations are stated against `SqueezeBench.Roth.f`,
`nMin` and the previous record `SqueezeBench.Roth.Upper.V002.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V002 was accepted; never edited.
-/

namespace SqueezeBench.Roth.Upper.V003

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V002.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V002.record record := sorry

end SqueezeBench.Roth.Upper.V003
