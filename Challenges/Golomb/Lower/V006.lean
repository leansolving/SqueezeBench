import SqueezeBench.Core
import SqueezeBench.Problems.Golomb.Records.Lower.V005.Def

/-!
# Challenge — Golomb, lower direction, V006

The trusted statement of record for version V006. `record` is the definition hole
`Records/Lower/V006/Def.lean` fills; the three obligations are stated against `SqueezeBench.Golomb.f`,
`nMin` and the previous record `SqueezeBench.Golomb.Lower.V005.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V005 was accepted; never edited.
-/

namespace SqueezeBench.Golomb.Lower.V006

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V005.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V005.record record := sorry

end SqueezeBench.Golomb.Lower.V006
