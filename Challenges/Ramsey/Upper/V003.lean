import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey.Records.Upper.V002.Def

/-!
# Challenge — Ramsey, upper direction, V003

The trusted statement of record for version V003. `record` is the definition hole
`Records/Upper/V003/Def.lean` fills; the three obligations are stated against `SqueezeBench.Ramsey.f`,
`nMin` and the previous record `SqueezeBench.Ramsey.Upper.V002.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V002 was accepted; never edited.
-/

namespace SqueezeBench.Ramsey.Upper.V003

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey.Upper.V002.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Upper.V002.record record := sorry

end SqueezeBench.Ramsey.Upper.V003
