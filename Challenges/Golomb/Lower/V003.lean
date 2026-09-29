import SqueezeBench.Core
import SqueezeBench.Problems.Golomb.Records.Lower.V002.Def

/-!
# Challenge — Golomb, lower direction, V003

The trusted statement of record for version V003. `record` is the definition hole
`Records/Lower/V003/Def.lean` fills; the three obligations are stated against `SqueezeBench.Golomb.f`,
`nMin` and the previous record `SqueezeBench.Golomb.Lower.V002.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V002 was accepted; never edited.
-/

namespace SqueezeBench.Golomb.Lower.V003

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V002.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V002.record record := sorry

end SqueezeBench.Golomb.Lower.V003
