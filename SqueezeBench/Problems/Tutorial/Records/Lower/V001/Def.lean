import SqueezeBench.Problems.Tutorial.Records.Lower.V000.Def

/-!
# Tutorial lower-bound record V001 — the record function

The patch idiom: `{1, 3, 4, 5}` is doubling-free, so `f 5 ≥ 4` where V000 claimed only `1`.

Submitted by Alice, 2026-08-04. Definitions only; the obligations are proved in `Proof.lean`.
-/

namespace SqueezeBench.Tutorial.Lower.V001

open SqueezeBench

def record : BoundFn := patch SqueezeBench.Tutorial.Lower.V000.record 5 4

end SqueezeBench.Tutorial.Lower.V001
