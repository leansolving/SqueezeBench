import SqueezeBench.Problems.Golomb.Def

/-!
# Golomb lower-bound record V000 — the record function

`f m ≥ C(m, 2) = m(m-1)/2`, by counting differences. No `pin`: the bound is already `0`
at `m = 0` and `m = 1`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V000

open SqueezeBench

/-- The seeded lower-bound record. No `pin`: the bound is `0` at `m = 0` and `m = 1`. -/
def record : BoundFn := fun m => m * (m - 1) / 2

end SqueezeBench.Golomb.Lower.V000
