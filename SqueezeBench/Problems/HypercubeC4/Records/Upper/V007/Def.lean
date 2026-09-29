import SqueezeBench.Problems.HypercubeC4.Records.Upper.V006.Def

/-! Record V007 for HypercubeC4, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V007

-- `3·(16·C(u,3) − u³)` for `u ≥ 4`, else `0`: the gain from `u` missing directions at a word.
def psi (u : ℕ) : ℕ := if 4 ≤ u then u * (5 * u - 4) * (u - 4) else 0

-- Three times Chung's weight of a word with `d` present and `u` missing directions.
def W (d u : ℕ) : ℕ := 32 * d * (d - 1) * (d - 2) + psi u

-- The slope of the secant of `d ↦ W d (n − d)` between `c` and `c + 1`.
def slope (n c : ℕ) : ℕ := W (c + 1) (n - c - 1) - W c (n - c)

-- The bound from the secant at `c`; the edge count of `Qₙ` when the slope is not positive.
def bound (n c : ℕ) : ℕ :=
  if 0 < slope n c then
    2 ^ (n - 1) * (8 * n * (n - 1) * (n - 2) + c * slope n c - W c (n - c)) / slope n c
  else n * 2 ^ (n - 1)

-- The least of `bound n 2, …, bound n (k + 2)`.
def best (n : ℕ) : ℕ → ℕ
  | 0 => bound n 2
  | k + 1 => min (best n k) (bound n (k + 3))

-- The best secant point `c` among `2, …, n + 2`; asymptotically `c ≈ 0.6228 n`.
def v : SqueezeBench.BoundFn := fun n => best n n

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.HypercubeC4.Upper.V006.record v

end SqueezeBench.HypercubeC4.Upper.V007
