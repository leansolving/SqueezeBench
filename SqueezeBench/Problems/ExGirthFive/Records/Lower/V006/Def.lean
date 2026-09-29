import SqueezeBench.Problems.ExGirthFive.Records.Lower.V005.Def

/-! Record V006 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V006

-- One prime just below each power of two from `2^4` to `2^19`.
def primes : List ℕ :=
  [11, 31, 61, 127, 251, 509, 1021, 2039, 4093, 8191, 16381, 32749, 65521, 131071, 262139, 524287]

-- For each prime `p` of the table, `⌊n/(2p²)⌋` disjoint copies of the point–line incidence graph
-- of the affine plane over `ZMod p`: `p²` points, `p²` lines `y = a x + b`, `p³` edges, girth 6.
-- Consecutive primes differ by a factor of about `2`, so the envelope of these linear bounds stays
-- within a constant factor of `(n/2)^{3/2}` up to `n = 2·524287²`.
def blocks : SqueezeBench.BoundFn := fun n =>
  (primes.map fun p => p * p * p * (n / (2 * p * p))).foldr max 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V005.record blocks

end SqueezeBench.ExGirthFive.Lower.V006
