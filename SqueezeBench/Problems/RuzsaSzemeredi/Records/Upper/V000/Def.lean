import SqueezeBench.Problems.RuzsaSzemeredi.Def

/-!
# Ruzsa–Szemerédi upper-bound record V000 — the record function

The ambient bound `C(n, 3)`: a graph on `n` vertices has only that many triples available to be
triangles.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V000

open SqueezeBench

/-- The seeded upper-bound record. -/
def record : BoundFn := fun n => n.choose 3

end SqueezeBench.RuzsaSzemeredi.Upper.V000
