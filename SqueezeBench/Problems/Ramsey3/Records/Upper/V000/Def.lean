import SqueezeBench.Problems.Ramsey3.Def

/-!
# `R(3,k)` upper-bound record V000 — the record function

The Erdős–Szekeres binomial bound at `s = 3`: `R(3,k) ≤ C(k+1, 2) = k(k+1)/2`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Ramsey3.Upper.V000

open SqueezeBench

/-- The seeded upper-bound record. No `pin`: below `nMin` the goal is `f k ≤ record k` with
`f k = 0`, which holds for any value. -/
def record : BoundFn := fun k => Nat.choose (k + 1) 2

end SqueezeBench.Ramsey3.Upper.V000
