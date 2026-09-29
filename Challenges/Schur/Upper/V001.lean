import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Upper.V000.Def

/-!
# Challenge — Schur, upper direction, V001

The trusted statement of record for version V001. `record` is the definition hole
`Records/Upper/V001/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Upper.V000.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V000 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Upper.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V000.record record := sorry

end SqueezeBench.Schur.Upper.V001
