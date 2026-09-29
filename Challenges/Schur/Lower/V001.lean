import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Lower.V000.Def

/-!
# Challenge — Schur, lower direction, V001

The trusted statement of record for version V001. `record` is the definition hole
`Records/Lower/V001/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Lower.V000.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V000 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Lower.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V000.record record := sorry

end SqueezeBench.Schur.Lower.V001
