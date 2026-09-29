import SqueezeBench.Core
import SqueezeBench.Problems.Golomb.Records.Upper.V003.Def

/-!
# Challenge — Golomb, upper direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Upper/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.Golomb.f`,
`nMin` and the previous record `SqueezeBench.Golomb.Upper.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.Golomb.Upper.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V003.record record := sorry

end SqueezeBench.Golomb.Upper.V004
