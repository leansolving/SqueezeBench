import SqueezeBench.Problems.ExGirthFive.Def

/-!
# ExGirthFive upper-bound record V000 — the record function

The ambient bound `C(n, 2)`: a graph on `n` vertices has only that many edges.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.ExGirthFive.Upper.V000

open SqueezeBench

/-- The seeded upper-bound record. -/
def record : BoundFn := fun n => n.choose 2

end SqueezeBench.ExGirthFive.Upper.V000
