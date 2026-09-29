import SqueezeBench.Problems.ExC4.Records.Lower.V006.Def

/-! Record V007 for ExC4, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V007

-- Edge counts of explicit `C₄`-free graphs on `8 ≤ n ≤ 49` vertices (the extremal graphs for
-- `n ≤ 40` and the best known ones for `41 ≤ n ≤ 49`, Afzaly–McKay), each stored as a table
-- of neighbourhood bitmasks in `Proof.lean` and checked there by the kernel.
def tbl : ℕ → ℕ
  | 8 => 11
  | 9 => 13
  | 10 => 16
  | 11 => 18
  | 12 => 21
  | 13 => 24
  | 14 => 27
  | 15 => 30
  | 16 => 33
  | 17 => 36
  | 18 => 39
  | 19 => 42
  | 20 => 46
  | 21 => 50
  | 22 => 52
  | 23 => 56
  | 24 => 59
  | 25 => 63
  | 26 => 67
  | 27 => 71
  | 28 => 76
  | 29 => 80
  | 30 => 85
  | 31 => 90
  | 32 => 92
  | 33 => 96
  | 34 => 102
  | 35 => 106
  | 36 => 110
  | 37 => 113
  | 38 => 117
  | 39 => 122
  | 40 => 127
  | 41 => 132
  | 42 => 137
  | 43 => 142
  | 44 => 148
  | 45 => 154
  | 46 => 157
  | 47 => 163
  | 48 => 168
  | 49 => 174
  | _ => 0

-- Greedy vertex deletion (`V006.delChain`) from a table graph on `a > n` vertices, `a ≤ 49`.
def anchorLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, a =>
    max (SqueezeBench.ExC4.Lower.V006.delChain (a - n) a (tbl a)) (anchorLoop n fuel (a + 1))
def anchorBest (n : ℕ) : ℕ := max (tbl n) (anchorLoop n (49 - n) (n + 1))

-- A bound for the vertices left over by a block decomposition.
def small (r : ℕ) : ℕ := max (SqueezeBench.ExC4.Lower.V006.record r) (anchorBest r)

-- `k = ⌊n / N q⌋` copies of `ER_q` joined by `k − 1` bridges, and a bridge to a graph on the
-- `n mod N q` remaining vertices when there are any: a bridge lies on no cycle.
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
  SqueezeBench.pin SqueezeBench.ExC4.nMin (fun n => max (anchorBest n) (blockBest n))

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.ExC4.Lower.V006.record v

end SqueezeBench.ExC4.Lower.V007
