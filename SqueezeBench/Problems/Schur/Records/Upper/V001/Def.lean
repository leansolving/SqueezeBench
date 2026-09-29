import SqueezeBench.Problems.Schur.Records.Upper.V000.Def

/-! Record V001 for Schur, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Schur/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Schur.Upper.V001

open SqueezeBench

-- `ram k` bounds the `k`-colour Ramsey number `R_k(3)` along the sharp pigeonhole
-- recurrence `R_k(3) ≤ k * (R_{k-1}(3) - 1) + 2`, started at `R_1(3) = 3`.
-- `ram 0 = 2`, `ram 1 = 3`, `ram 2 = 6`, `ram 3 = 17`, `ram 4 = 66`, `ram 5 = 327`;
-- `ram k = ⌊e * k!⌋ + 1` for `k ≥ 1`.
def ram (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 2 (fun j a => (j + 1) * (a - 1) + 2) k

-- `S(k) ≤ R_k(3) - 2 = ⌊e * k!⌋ - 1`.
def record : SqueezeBench.BoundFn := fun k => ram k - 2

end SqueezeBench.Schur.Upper.V001
