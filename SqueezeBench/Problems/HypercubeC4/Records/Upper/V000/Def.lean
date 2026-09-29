import SqueezeBench.Problems.HypercubeC4.Def

/-!
# HypercubeC4 upper-bound record V000 — the record function

The ambient bound `C(2ⁿ, 2)`: a graph on the `2ⁿ` words has only that many edges.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.HypercubeC4.Upper.V000

open SqueezeBench

/-- The seeded upper-bound record. -/
def record : BoundFn := fun n => (2 ^ n).choose 2

end SqueezeBench.HypercubeC4.Upper.V000
