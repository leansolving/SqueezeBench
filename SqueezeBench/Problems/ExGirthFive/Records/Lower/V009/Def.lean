import SqueezeBench.Problems.ExGirthFive.Records.Lower.V008.Def

/-! Record V009 for ExGirthFive, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V009.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V009

-- Binary search for `⌊√x⌋` on `[lo, hi]`, by structural recursion on a fuel (`x` itself is enough,
-- since the bracket halves at every step); the kernel peels only `O(log x)` steps off the fuel.
-- It keeps `x < (hi+1)²` and returns `hi`, so its result brackets `√x` from above whatever the fuel.
def sqrtAux (x : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    if hi ≤ lo then hi else
      if (lo + hi + 1) / 2 * ((lo + hi + 1) / 2) ≤ x then sqrtAux x fuel ((lo + hi + 1) / 2) hi
      else sqrtAux x fuel lo ((lo + hi + 1) / 2 - 1)

def sqrtUp (x : ℕ) : ℕ := sqrtAux x x 0 x

-- The tail, valid for every `n`: with `q = ⌊√(n/2)⌋`, Bertrand's postulate gives a prime `p` with
-- `q < p ≤ 2q`, and the sub-plane of `AG(2,p)` with `⌊n/(4q)⌋ ≤ p` slope classes and `⌊n/2⌋ ≤ p²`
-- points fits in `n` vertices whichever `p` it is. About `(n/2)^{3/2} / 2` edges.
def tail : SqueezeBench.BoundFn := fun n => (n / (4 * sqrtUp (n / 2))) * (n / 2)

-- The sub-plane with `s` slope classes on `r` leftover vertices, its points clipped to the `p²`
-- available: `s · min (r − s·p) p²` edges.
def cand (p r s : ℕ) : ℕ := s * min (r - s * p) (p * p)

-- The better of the two integer neighbours of the balanced choice `s = r/(2p)`; V008 took the
-- ceiling only, which loses up to `r/2` edges when `r` is just above a multiple of `2p`.
def part2 (p r : ℕ) : ℕ := max (cand p r (r / (2 * p))) (cand p r (r / (2 * p) + 1))

def blk2 (p n : ℕ) : ℕ := p * p * p * (n / (2 * p * p)) + part2 p (n % (2 * p * p))

-- The V008 table of primes, with the improved leftover.
def blocks2 : SqueezeBench.BoundFn := fun n =>
  (SqueezeBench.ExGirthFive.Lower.V008.primes.map fun p => blk2 p n).foldr max 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V008.record fun n => max (blocks2 n) (tail n)

end SqueezeBench.ExGirthFive.Lower.V009
