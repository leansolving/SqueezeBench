import SqueezeBench.Problems.Roth.Def

/-!
# Roth lower-bound record V000 — the record function

`min n 2`: the singleton `{0}` is 3-AP-free, and so is `{0, 1}` — a nontrivial progression
needs three distinct terms.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Roth.Lower.V000

open SqueezeBench

/-- The seeded lower-bound record. -/
def record : BoundFn := pin nMin (fun n => min n 2)

end SqueezeBench.Roth.Lower.V000
