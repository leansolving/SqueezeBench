import SqueezeBench.Core
import SqueezeBench.Problems.RuzsaSzemeredi.Def

/-!
# Challenge — RuzsaSzemeredi, lower direction, V000

The trusted statement of the seed record. `record` is the definition hole
`Records/Lower/V000/Def.lean` fills; `valid` is stated against `SqueezeBench.RuzsaSzemeredi.f`, fully qualified
so that no `open` in the record can redirect it. A seed has no predecessor, so there is
nothing to improve on. Never edited.
-/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V000

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record := sorry

end SqueezeBench.RuzsaSzemeredi.Lower.V000
