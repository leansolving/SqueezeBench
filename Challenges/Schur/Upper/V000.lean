import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Def

/-!
# Challenge — Schur, upper direction, V000

The trusted statement of the seed record. `record` is the definition hole
`Records/Upper/V000/Def.lean` fills; `valid` is stated against `SqueezeBench.Schur.f`, fully qualified
so that no `open` in the record can redirect it. A seed has no predecessor, so there is
nothing to improve on. Never edited.
-/

namespace SqueezeBench.Schur.Upper.V000

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := sorry

end SqueezeBench.Schur.Upper.V000
