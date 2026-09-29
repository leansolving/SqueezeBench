import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Lower.V001.Def

/-!
# Challenge — Schur, lower direction, V002

The trusted statement of record for version V002. `record` is the definition hole
`Records/Lower/V002/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Lower.V001.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V001 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Lower.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V001.record record := sorry

end SqueezeBench.Schur.Lower.V002
