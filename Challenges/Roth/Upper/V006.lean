import SqueezeBench.Core
import SqueezeBench.Problems.Roth.Records.Upper.V005.Def

/-!
# Challenge — Roth, upper direction, V006

The trusted statement of record for version V006. `record` is the definition hole
`Records/Upper/V006/Def.lean` fills; the three obligations are stated against `SqueezeBench.Roth.f`,
`nMin` and the previous record `SqueezeBench.Roth.Upper.V005.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V005 was accepted; never edited.
-/

namespace SqueezeBench.Roth.Upper.V006

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V005.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V005.record record := sorry

end SqueezeBench.Roth.Upper.V006
