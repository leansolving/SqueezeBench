import SqueezeBench.Problems.Tutorial.Def

/-!
# Tutorial lower-bound record V000 — the record function

The seeded baseline: `{1}` is doubling-free whenever the parameter is at least `nMin`,
so `1` is a lower bound there.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Tutorial.Lower.V000

open SqueezeBench

def record : BoundFn := fun m => if m < nMin then 0 else 1

end SqueezeBench.Tutorial.Lower.V000
