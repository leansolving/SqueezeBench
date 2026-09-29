import SqueezeBench.Problems.Ramsey.Def

/-!
# Ramsey upper-bound record V000 — the record function

The Erdős–Szekeres binomial bound `C(2n-2, n-1)`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Ramsey.Upper.V000

open SqueezeBench

def record : BoundFn := fun n => Nat.choose (2 * n - 2) (n - 1)

end SqueezeBench.Ramsey.Upper.V000
