import SqueezeBench.Problems.Schur.Def

/-!
# Schur lower-bound record V000 — the record function

The ternary colouring is sum-free on each part of `{1, …, (3ᵏ-1)/2}`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Schur.Lower.V000

open SqueezeBench

def record : BoundFn := fun k => (3 ^ k - 1) / 2

end SqueezeBench.Schur.Lower.V000
