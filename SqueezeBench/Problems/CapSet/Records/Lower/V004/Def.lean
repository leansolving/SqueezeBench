import SqueezeBench.Problems.CapSet.Records.Lower.V003.Def

/-! Record V004 for CapSet, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Lower/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Lower.V004

-- Verified caps `(dimension, size)`: the exact values up to dimension 6, then caps of size
-- 236 (Calderbank–Fishburn), 512 and 1082 (FunSearch) in dimensions 7, 8 and 9.
def tbl : List (ℕ × ℕ) :=
  [(1, 2), (2, 4), (3, 9), (4, 20), (5, 45), (6, 112), (7, 236), (8, 512), (9, 1082)]

-- Given `[b (k-1), …, b 0]`, the best product `s · b (k - d)` over the table.
def step (prev : List ℕ) : ℕ :=
  tbl.foldl (fun acc p => max acc (p.2 * prev.getD (p.1 - 1) 0)) 0

-- `dp n = [b n, b (n-1), …, b 0]` with `b 0 = 1`: the best product of table caps in each dimension.
def dp : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => step (dp k) :: dp k

def best (n : ℕ) : ℕ := (dp n).headD 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.CapSet.Lower.V003.record
    (SqueezeBench.pin SqueezeBench.CapSet.nMin best)

end SqueezeBench.CapSet.Lower.V004
