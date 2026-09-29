import SqueezeBench.Problems.ExC4.Records.Lower.V007.Def

/-! Record V008 for ExC4, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V008.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V008

-- The sub-polarity graph on `c` of the `q` columns of `ER_q` (`1 ≤ c ≤ q − 1`): the affine
-- points of `c` columns, their `c` points at infinity and the point `none`, so `cq + c + 1`
-- vertices, with at least `(c²q + 2cq + c + 1)/2` edges.
def colN (q c : ℕ) : ℕ := c * q + c + 1
def colVal (q c : ℕ) : ℕ := (c * c * q + 2 * c * q + c + 1) / 2

-- Greedy deletion (`V006.delChain`) from the smallest such graph with at least `n` vertices.
def colDel (q n : ℕ) : ℕ :=
  if (n + q - 1) / (q + 1) + 1 ≤ q ∧ n ≤ colN q ((n + q - 1) / (q + 1)) then
    SqueezeBench.ExC4.Lower.V006.delChain (colN q ((n + q - 1) / (q + 1)) - n)
      (colN q ((n + q - 1) / (q + 1))) (colVal q ((n + q - 1) / (q + 1)))
  else 0

-- Best over the prime powers `q` with `q² ≤ 2n`.
def colLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
    if q * q ≤ 2 * n then
      max (if SqueezeBench.ExC4.Lower.V006.isPrimePowB q then colDel q n else 0)
        (colLoop n fuel (q + 1))
    else 0
def colBest (n : ℕ) : ℕ := colLoop n n 2

-- V007's block decomposition with bridges, the new bound available for the leftover vertices.
def small (r : ℕ) : ℕ := max (SqueezeBench.ExC4.Lower.V007.record r) (colBest r)
def blockVal (q n : ℕ) : ℕ :=
  if SqueezeBench.ExC4.Lower.V006.N q ≤ n then
    (n / SqueezeBench.ExC4.Lower.V006.N q) * SqueezeBench.ExC4.Lower.V006.E q
      + (n / SqueezeBench.ExC4.Lower.V006.N q - 1)
      + small (n % SqueezeBench.ExC4.Lower.V006.N q)
      + (if n % SqueezeBench.ExC4.Lower.V006.N q = 0 then 0 else 1)
  else 0
def blockLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
    if q * q ≤ n then
      max (if SqueezeBench.ExC4.Lower.V006.isPrimePowB q then blockVal q n else 0)
        (blockLoop n fuel (q + 1))
    else 0
def blockBest (n : ℕ) : ℕ := blockLoop n n 2

def v : SqueezeBench.BoundFn :=
  SqueezeBench.pin SqueezeBench.ExC4.nMin (fun n => max (colBest n) (blockBest n))

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.ExC4.Lower.V007.record v

end SqueezeBench.ExC4.Lower.V008
