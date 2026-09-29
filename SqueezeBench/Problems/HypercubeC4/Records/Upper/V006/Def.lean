import SqueezeBench.Problems.HypercubeC4.Records.Upper.V005.Def

/-! Record V006 for HypercubeC4, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V006

-- Third moment of the degrees, secant of `C(·, 3)` at `c`: `⌊2ⁿ⁻²(n(n−1)(n−2) + 8(c−1)c(c+1)) / (6c(c−1))⌋`.
def bound (n c : ℕ) : ℕ :=
  2 ^ (n - 2) * (n * (n - 1) * (n - 2) + 8 * (c - 1) * c * (c + 1)) / (6 * c * (c - 1))

-- The least of `bound n 2, …, bound n (k + 2)`.
def best (n : ℕ) : ℕ → ℕ
  | 0 => bound n 2
  | k + 1 => min (best n k) (bound n (k + 3))

-- The best secant point `c` among `2, …, n + 2`; asymptotically `c ≈ n / ∛4`.
def v : SqueezeBench.BoundFn := fun n => best n n

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.HypercubeC4.Upper.V005.record v

end SqueezeBench.HypercubeC4.Upper.V006
