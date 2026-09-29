import SqueezeBench.Core
import SqueezeBench.Problems.Ramsey3.Records.Upper.V001.Def

/-!
# Challenge — Ramsey3, upper direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Upper/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.Ramsey3.f`,
`nMin` and the previous record `SqueezeBench.Ramsey3.Upper.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.Ramsey3.Upper.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey3.Upper.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Upper.V001.record record := sorry

end SqueezeBench.Ramsey3.Upper.V002
