import SqueezeBench.Problems.ExC4.Records.Upper.V003.Def

/-! Record V004 for ExC4, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Upper/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Upper.V004

-- The restricted cherry count around a vertex of degree `d`, with the chord of `a(a − 1)` between
-- `p` and `p + 1`: from `4pm ≤ 2pd + (n − 1)p(p + 3) + (n − d)(n − d − 1)`.
def bp (n d p : ℕ) : ℕ := (2 * p * d + (n - 1) * (p * (p + 3)) + (n - d) * (n - d - 1)) / (4 * p)

-- The chord level: one below the average degree V003 still allows, and at least `1`.
def pOf (n : ℕ) : ℕ := max 1 (2 * SqueezeBench.ExC4.Upper.V003.record n / n - 1)

-- What a graph of maximum degree `d` can have: `nd/2` edges, and the restricted count.
def cand (n d p : ℕ) : ℕ := min (n * d / 2) (bp n d p)

-- The largest candidate over the maximum degrees `d < k`.
def scanMax (n p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => max (scanMax n p k) (cand n k p)

def v : SqueezeBench.BoundFn := fun n => scanMax n (pOf n) n

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExC4.Upper.V003.record v

end SqueezeBench.ExC4.Upper.V004
