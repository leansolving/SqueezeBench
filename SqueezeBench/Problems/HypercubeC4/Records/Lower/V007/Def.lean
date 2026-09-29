import SqueezeBench.Problems.HypercubeC4.Records.Lower.V006.Def

/-! Record V007 for HypercubeC4, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V007

-- Brass–Harborth–Nienborg with mixed block sizes. With `m = 4^r ≤ n < 4^(r+1)` and
-- `n − m = 3t + d`, blow `t` coordinates of `Q_m` up into blocks of size 4, one into a block of
-- size `d + 1` and keep the other `m − t − 1`: `n·2^(n−2) + (m + t)·2^(n−2−r) + [d = 2]·2^(n−3−r)`
-- edges, i.e. `(n + (m + t + ½[d = 2])/2^r)·2^(n−2)`, for `n ≥ 4`.
def mixed : SqueezeBench.BoundFn := fun n =>
  if n < 4 then 0 else
    n * 2 ^ (n - 2) + (4 ^ Nat.log 4 n + (n - 4 ^ Nat.log 4 n) / 3) * 2 ^ (n - 2 - Nat.log 4 n)
      + (if (n - 4 ^ Nat.log 4 n) % 3 = 2 then 2 ^ (n - 3 - Nat.log 4 n) else 0)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.HypercubeC4.Lower.V006.record mixed

end SqueezeBench.HypercubeC4.Lower.V007
