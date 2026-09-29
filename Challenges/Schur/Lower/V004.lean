import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Lower.V003.Def

/-!
# Challenge — Schur, lower direction, V004

The trusted statement of record for version V004. `record` is the definition hole
`Records/Lower/V004/Def.lean` fills; the three obligations are stated against `SqueezeBench.Schur.f`,
`nMin` and the previous record `SqueezeBench.Schur.Lower.V003.record`, fully qualified so that no
`open` in the record can redirect them. Written once, when V003 was accepted; never edited.
-/

namespace SqueezeBench.Schur.Lower.V004

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V003.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V003.record record := sorry

end SqueezeBench.Schur.Lower.V004
