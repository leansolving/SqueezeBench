import SqueezeBench.Core
import SqueezeBench.Problems.Schur.Records.Lower.V000.Def

/-!
# Schur lower-bound record V001 — the record function

`S(4) = 44` is known exactly (Golomb & Baumert 1965). Starting the tripling recurrence
`S(k+1) ≥ 3·S(k) + 1` from an explicit sum-free 4-colouring of `[1, 44]` instead of from
the empty colouring replaces the seed's `(3ᵏ − 1)/2` by `(89·3^(k−4) − 1)/2` for `k ≥ 4`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Schur.Lower.V001

open SqueezeBench

-- The tripling tower started at `S(4) ≥ 44`; `2·44 + 1 = 89`.
def v : BoundFn := SqueezeBench.pin 4 (fun k => (89 * 3 ^ (k - 4) - 1) / 2)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Schur.Lower.V000.record v

end SqueezeBench.Schur.Lower.V001
