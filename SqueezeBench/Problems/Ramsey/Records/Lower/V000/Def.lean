import SqueezeBench.Problems.Ramsey.Def

/-!
# Ramsey lower-bound record V000 — the record function

The block construction on `(n-1)²` vertices forces neither a clique nor an independent set of size `n`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Ramsey.Lower.V000

open SqueezeBench

def record : BoundFn := pin nMin (fun n => (n - 1) ^ 2 + 1)

end SqueezeBench.Ramsey.Lower.V000
