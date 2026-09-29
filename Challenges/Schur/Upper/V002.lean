import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Upper.V001.Def

/-!
# Challenge — Schur, upper direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Upper/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Upper.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Upper.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V001.record record := sorry

end SqueezeBench.Schur.Upper.V002
