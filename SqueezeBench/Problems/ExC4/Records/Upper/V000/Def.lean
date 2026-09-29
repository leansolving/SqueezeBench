import SqueezeBench.Problems.ExC4.Def

/-!
# ExC4 upper-bound record V000 — the record function

The ambient bound `C(n, 2)`: a graph on `n` vertices has only that many edges.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.ExC4.Upper.V000

open SqueezeBench

/-- The seeded upper-bound record. -/
def record : BoundFn := fun n => n.choose 2

end SqueezeBench.ExC4.Upper.V000
