import SqueezeBench.Problems.Roth.Def

/-!
# Roth upper-bound record V000 — the record function

The ambient bound `r₃(n) ≤ n`: a subset of `{0, …, n-1}` has at most `n` elements.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Roth.Upper.V000

open SqueezeBench

/-- The seeded upper-bound record. No `pin`: below `nMin` the goal is `f n ≤ record n` with
`f n = 0`, which holds for any value. -/
def record : BoundFn := fun n => n

end SqueezeBench.Roth.Upper.V000
