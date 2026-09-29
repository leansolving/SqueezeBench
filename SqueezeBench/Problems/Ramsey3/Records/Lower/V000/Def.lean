import SqueezeBench.Problems.Ramsey3.Def

/-!
# `R(3,k)` lower-bound record V000 — the record function

`R(3,k) ≥ 2k - 1`: the parity graph on `2k-2` vertices is triangle-free, and a clique in its
complement has constant parity, so there are at most `k-1` of them.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Ramsey3.Lower.V000

open SqueezeBench

/-- The seeded lower-bound record. -/
def record : BoundFn := pin nMin (fun k => 2 * k - 1)

end SqueezeBench.Ramsey3.Lower.V000
