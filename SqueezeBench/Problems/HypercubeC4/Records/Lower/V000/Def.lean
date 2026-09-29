import SqueezeBench.Problems.HypercubeC4.Def

/-!
# HypercubeC4 lower-bound record V000 — the record function

The trivial bound `0`: the empty graph qualifies.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.HypercubeC4.Lower.V000

open SqueezeBench

/-- The seeded lower-bound record. -/
def record : BoundFn := fun _ => 0

end SqueezeBench.HypercubeC4.Lower.V000
