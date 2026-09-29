import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Upper.V002.Def

/-!
# Challenge — Schur, upper direction, V003

The trusted statement of record for version V003. `record` is the definition hole
`Records/Upper/V003/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Upper.V002.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V002 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Upper.V003

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V002.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V002.record record := sorry

end SqueezeBench.Schur.Upper.V003
