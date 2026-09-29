import SqueezeBench.Problems.CapSet.Def

/-!
# CapSet upper-bound record V000 — the record function

The Ellenberg–Gijswijt style bound `2·3^(n-1)`, with `1` at `n = 0`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.CapSet.Upper.V000

open SqueezeBench

def record : BoundFn := fun n => if n = 0 then 1 else 2 * 3 ^ (n - 1)

end SqueezeBench.CapSet.Upper.V000
