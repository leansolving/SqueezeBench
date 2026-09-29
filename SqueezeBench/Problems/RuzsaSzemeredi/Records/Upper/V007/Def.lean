import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V006.Def

/-! Record V007 for RuzsaSzemeredi, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V007

-- Twice the largest possible sum of the triangle counts over the `2t` neighbours of a vertex
-- with `t` triangles, in a locally linear graph on `n` vertices with `T` triangles: every
-- triangle meets the closed neighbourhood of the vertex (`Σ ≤ T + t`), and the triangle counts
-- of a triangle add up to at most `(n + 2 + n % 2) / 2` (`Σ ≤ t(n + 2 + n % 2)/2 − t²`).
def cap (n T t : ℕ) : ℕ := min (2 * T + 2 * t) (t * (n + 2 + n % 2) - 2 * t * t)

-- The test a triangle count `T` must pass. Summing the neighbourhood bound over all vertices
-- gives `4 Σ t_v² ≤ Σ cap t_v`; the left side minus the right side is a convex function of each
-- `t_v`, so with `3T = qn + r` the most balanced counts (`n − r` vertices with `q`, `r` with
-- `q + 1`) minimise it, and they must still give at most `0`.
def ok (n T : ℕ) : Bool :=
  let q := 3 * T / n
  let r := 3 * T % n
  decide ((n - r) * (4 * q * q) + r * (4 * (q + 1) * (q + 1))
    ≤ (n - r) * cap n T q + r * cap n T (q + 1))

-- The largest `T' ≤ T` passing the test (`0` if none).
def search (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => cond (ok n (T + 1)) (T + 1) (search n T)

def record : SqueezeBench.BoundFn :=
  fun n => search n (SqueezeBench.RuzsaSzemeredi.Upper.V006.record n)

end SqueezeBench.RuzsaSzemeredi.Upper.V007
