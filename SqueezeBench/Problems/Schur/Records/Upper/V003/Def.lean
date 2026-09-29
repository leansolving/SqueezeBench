import SqueezeBench.Problems.Schur.Records.Upper.V002.Def

/-! Record V003 for Schur, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Schur/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Schur.Upper.V003

open SqueezeBench

-- For odd `k ≥ 3` the neighbourhood bound at the midpoint vertex `N / 2` of the gap
-- colouring is even, while `ram (k-1) - 1` is odd; that loses one per colour, so the
-- Ramsey-chain bound `ram k - 2` drops to `ram k - k - 1`. At `k = 3` this is `13 = S(3)`.
def record : SqueezeBench.BoundFn := fun k =>
  if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - k - 1 else V001.ram k - 2

end SqueezeBench.Schur.Upper.V003
