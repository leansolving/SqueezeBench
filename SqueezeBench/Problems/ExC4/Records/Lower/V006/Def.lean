import SqueezeBench.Problems.ExC4.Records.Lower.V005.Def

/-! Record V006 for ExC4, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V006

-- Trial division: `p ≥ 2` with no divisor `d ∈ [2, p)`.
def isPrimeB (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range' 2 (p - 2)).all (fun d => decide (p % d ≠ 0))

-- Is `q` a power of `p`? Repeated division, with fuel.
def isPowOf (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, q => q == 1 || (decide (q % p = 0) && isPowOf p fuel (q / p))

-- Is `q` a prime power? Some prime `p ∈ [2, q]` has `q` among its powers.
def isPrimePowB (q : ℕ) : Bool :=
  (List.range' 2 (q - 1)).any (fun p => isPrimeB p && isPowOf p q q)

-- The polarity graph `ER_q` of `PG(2, q)`: `q² + q + 1` vertices and `q (q + 1)² / 2` edges.
def N (q : ℕ) : ℕ := q * q + q + 1
def E (q : ℕ) : ℕ := q * (q + 1) * (q + 1) / 2

-- Greedy vertex deletion: a `C₄`-free graph with `m` edges on `t` vertices has a vertex of
-- degree at most `⌊2m/t⌋`; deleting it keeps `m - ⌊2m/t⌋` edges. Iterated `j` times.
def delChain : ℕ → ℕ → ℕ → ℕ
  | 0, _, m => m
  | j + 1, t, m => delChain j (t - 1) (m - 2 * m / t)

-- `ER_q` with `N q - n` vertices deleted, when `n ≤ N q`.
def delVal (q n : ℕ) : ℕ := if n ≤ N q then delChain (N q - n) (N q) (E q) else 0

-- Best deletion bound over the prime powers `q` with `q² ≤ 2n`.
def delLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
    if q * q ≤ 2 * n then
      max (if isPrimePowB q then delVal q n else 0) (delLoop n fuel (q + 1))
    else 0
def delBest (n : ℕ) : ℕ := delLoop n n 2

-- A bound for the vertices left over by a block decomposition.
def small (r : ℕ) : ℕ := max (SqueezeBench.ExC4.Lower.V005.record r) (delBest r)

-- `⌊n / N q⌋` disjoint copies of `ER_q`, plus a graph on the `n mod N q` remaining vertices.
def blockVal (q n : ℕ) : ℕ := if N q ≤ n then (n / N q) * E q + small (n % N q) else 0

-- Best block bound over the prime powers `q` with `q² ≤ n`.
def blockLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
    if q * q ≤ n then
      max (if isPrimePowB q then blockVal q n else 0) (blockLoop n fuel (q + 1))
    else 0
def blockBest (n : ℕ) : ℕ := blockLoop n n 2

-- Both loops give `0` at `n = 0`, so the bound vanishes below `nMin = 1`.
def v : SqueezeBench.BoundFn := fun n => max (blockBest n) (delBest n)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.ExC4.Lower.V005.record v

end SqueezeBench.ExC4.Lower.V006
