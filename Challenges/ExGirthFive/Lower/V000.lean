import SqueezeBench.Core
import SqueezeBench.Problems.ExGirthFive.Def

/-!
# Challenge — ExGirthFive, lower direction, V000

The trusted statement of the seed record. `record` is the definition hole
`Records/Lower/V000/Def.lean` fills; `valid` is stated against `SqueezeBench.ExGirthFive.f`, fully qualified
so that no `open` in the record can redirect it. A seed has no predecessor, so there is
nothing to improve on. Never edited.
-/

namespace SqueezeBench.ExGirthFive.Lower.V000

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record := sorry

end SqueezeBench.ExGirthFive.Lower.V000
