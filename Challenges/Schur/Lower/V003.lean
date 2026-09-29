import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Lower.V002.Def

/-!
# Challenge — Schur, lower direction, V003

The trusted statement of record for version V003. `record` is the definition hole
`Records/Lower/V003/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Lower.V002.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V002 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Lower.V003

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V002.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V002.record record := sorry

end SqueezeBench.Schur.Lower.V003
