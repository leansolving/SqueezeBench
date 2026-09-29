import SqueezeBench.Problems.CapSet.Def

/-!
# CapSet lower-bound record V000 — the record function

`{0,1}ⁿ ⊆ 𝔽₃ⁿ` is three-AP-free and has `2ⁿ` elements.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.CapSet.Lower.V000

open SqueezeBench

def record : BoundFn := pin nMin (fun n => 2 ^ n)

end SqueezeBench.CapSet.Lower.V000
