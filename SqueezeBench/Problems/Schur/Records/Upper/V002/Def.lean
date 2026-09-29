import SqueezeBench.Problems.Schur.Records.Upper.V001.Def

/-! Record V002 for Schur, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Schur/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Schur.Upper.V002

open SqueezeBench

-- `V001.ram k - 2 = ⌊e * k!⌋ - 1` is the Ramsey-chain bound. For odd `k ≥ 3` a reflection
-- and parity argument on the extremal case removes one more: `⌊e * k!⌋ - 2`.
def record : SqueezeBench.BoundFn := fun k =>
  if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - 3 else V001.ram k - 2

end SqueezeBench.Schur.Upper.V002
