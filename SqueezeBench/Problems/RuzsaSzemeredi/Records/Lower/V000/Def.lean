import SqueezeBench.Problems.RuzsaSzemeredi.Def

/-!
# Ruzsa–Szemerédi lower-bound record V000 — the record function

The constant `1`: a single triangle is locally linear.

Deliberately weak. See the problem README for why the natural next bound, `n / 3` from disjoint
triangles, is the first improvement, and why Mathlib's own lower bound cannot be a record.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V000

open SqueezeBench

/-- The seeded lower-bound record. -/
def record : BoundFn := pin nMin (fun _ => 1)

end SqueezeBench.RuzsaSzemeredi.Lower.V000
