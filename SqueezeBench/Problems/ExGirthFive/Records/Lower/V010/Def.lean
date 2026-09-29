import SqueezeBench.Problems.ExGirthFive.Records.Lower.V009.Def

/-! Record V010 for ExGirthFive, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V010.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V010

-- The projective plane `PG(2,p)` has `p² + p + 1` points and as many lines; its point–line
-- incidence graph has `N p` vertices and `E p` edges (every point is on `p + 1` lines), girth `6`.
def N (p : ℕ) : ℕ := 2 * (p * p + p + 1)
def E (p : ℕ) : ℕ := (p + 1) * (p * p + p + 1)

-- An induced subgraph of `PG(2,p)` on at most `r` vertices: `s` pencils (all `s·p` lines through
-- `s` points at infinity, and those points), `m` affine points and the line at infinity, with
-- `m + s·(p+1) + 1 ≤ r` and `m ≤ p²`. Every affine point is on one line of each pencil, so it has
-- `s·(m + p + 1)` edges. `0` when the `s` pencils alone do not fit.
def candB (p r s : ℕ) : ℕ :=
  if s * (p + 1) + 1 ≤ r then s * (min (r - 1 - s * (p + 1)) (p * p) + p + 1) else 0

-- The better of the two integer neighbours of the balanced number of pencils `(r + p)/(2(p+1))`.
def part3 (p r : ℕ) : ℕ :=
  max (candB p r ((r + p) / (2 * (p + 1)))) (candB p r ((r + p) / (2 * (p + 1)) + 1))

-- `⌊n / N p⌋` full projective planes and a partial one on the `n mod N p` leftover vertices.
def blk3 (p n : ℕ) : ℕ := E p * (n / N p) + part3 p (n % N p)

-- Over the V008 table of primes.
def blocks3 : SqueezeBench.BoundFn := fun n =>
  (SqueezeBench.ExGirthFive.Lower.V008.primes.map fun p => blk3 p n).foldr max 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V009.record blocks3

end SqueezeBench.ExGirthFive.Lower.V010
