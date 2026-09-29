import SqueezeBench.Problems.Schur.Def

/-!
# Schur upper-bound record V000 — the record function

The factorial bound `3·k! - 2`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Schur.Upper.V000

open SqueezeBench

def record : BoundFn := fun k => 3 * Nat.factorial k - 2

end SqueezeBench.Schur.Upper.V000
