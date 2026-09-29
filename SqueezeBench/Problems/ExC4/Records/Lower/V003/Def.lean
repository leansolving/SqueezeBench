import SqueezeBench.Problems.ExC4.Records.Lower.V002.Def

/-! Record V003 for ExC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V003

-- `⌊n/21⌋` disjoint copies of the Erdős–Rényi polarity graph of PG(2,4): 21 vertices,
-- 50 edges, `C₄`-free. Folded into V002 with `maxWith`, which wins from `n = 21` on.
def blocks : SqueezeBench.BoundFn := fun n => 50 * (n / 21)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExC4.Lower.V002.record blocks

end SqueezeBench.ExC4.Lower.V003
