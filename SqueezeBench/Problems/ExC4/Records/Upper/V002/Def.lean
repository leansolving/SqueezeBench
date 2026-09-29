import SqueezeBench.Problems.ExC4.Records.Upper.V001.Def

/-! Record V002 for ExC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Upper.V002

-- `C(a, 2)`, written so the kernel evaluates it in one multiplication and one division.
def c2 (a : ℕ) : ℕ := a * (a - 1) / 2

-- The cherry count with an integral degree sequence: if a `C₄`-free graph on `n` vertices has
-- degree sum `S`, then with `q = ⌊S/n⌋` convexity forces `n·C(q,2) + q·S ≤ C(n,2) + n·q²`.
def cherryOk (n S : ℕ) : Bool :=
  n * c2 (S / n) + (S / n) * S ≤ c2 n + n * (S / n) * (S / n)

-- Reiman's value, lowered by one edge wherever it fails the integrality test.
def record : SqueezeBench.BoundFn := fun n =>
  if cherryOk n (2 * SqueezeBench.ExC4.Upper.V001.record n)
    then SqueezeBench.ExC4.Upper.V001.record n
    else SqueezeBench.ExC4.Upper.V001.record n - 1

end SqueezeBench.ExC4.Upper.V002
