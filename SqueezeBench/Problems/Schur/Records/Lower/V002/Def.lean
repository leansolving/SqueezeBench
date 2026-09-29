import SqueezeBench.Problems.Schur.Records.Lower.V001.Def

/-! Record V002 for Schur, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Schur/Lower/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The bound is the best value obtainable from the explicit sum-free partitions of `[1, N]` for
`N = 1, 4, 13, 44, 160, 536, 1680` (`k = 1, …, 7`) by iterating the four template steps
`S(k+1) ≥ 3·S(k) + 1`, `S(k+3) ≥ 33·S(k) + 6`, `S(k+4) ≥ 111·S(k) + 43` and
`S(k+5) ≥ 380·S(k) + 148` (Rowley 2021; Ageron, Casteras, Pellerin, Portella, Rimmel,
Tomasik 2022). `H` is the dynamic programme over the last step taken. -/

namespace SqueezeBench.Schur.Lower.V002

-- The bound: base partitions for `k ≤ 7`, then the best of the four template steps.
def H : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 13
  | 4 => 44
  | 5 => 160
  | 6 => 536
  | 7 => 1680
  | k + 8 => max (3 * H (k + 7) + 1)
      (max (33 * H (k + 5) + 6) (max (111 * H (k + 4) + 43) (380 * H (k + 3) + 148)))

def v : SqueezeBench.BoundFn := H

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Schur.Lower.V001.record v

end SqueezeBench.Schur.Lower.V002
