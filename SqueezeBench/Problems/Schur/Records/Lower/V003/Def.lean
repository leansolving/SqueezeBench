import SqueezeBench.Problems.Schur.Records.Lower.V002.Def

/-! Record V003 for Schur, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Schur/Lower/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

V002's dynamic programme with two additions: the base `S(7) ≥ 1696` (Rowley 2021) in place of
`1680`, and the shifted-template step `S(k+2) ≥ 10·S(k) + 2` (Bengone, Brouk, Grinsztajn,
Helbert, Lugherini, Rimmel, Tomasik 2026) beside the steps `3·S(k)+1`, `33·S(k)+6`,
`111·S(k)+43`, `380·S(k)+148`. -/

namespace SqueezeBench.Schur.Lower.V003

-- The bound: base partitions for `k ≤ 7`, then the best of the five template steps.
def H : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 13
  | 4 => 44
  | 5 => 160
  | 6 => 536
  | 7 => 1696
  | k + 8 => max (3 * H (k + 7) + 1) (max (10 * H (k + 6) + 2) (max (33 * H (k + 5) + 6)
      (max (111 * H (k + 4) + 43) (380 * H (k + 3) + 148))))

def v : SqueezeBench.BoundFn := H

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Schur.Lower.V002.record v

end SqueezeBench.Schur.Lower.V003
