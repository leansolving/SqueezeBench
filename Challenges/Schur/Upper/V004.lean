import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Upper.V003.Def

/-!
# Challenge — Schur, upper direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Upper/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Upper.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Upper.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V003.record record := sorry

end SqueezeBench.Schur.Upper.V004
