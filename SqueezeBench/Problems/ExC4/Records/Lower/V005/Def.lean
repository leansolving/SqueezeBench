import SqueezeBench.Problems.ExC4.Records.Lower.V004.Def

/-! Record V005 for ExC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V005

-- `⌊n/57⌋` disjoint copies of the Erdős–Rényi polarity graph of PG(2,7): 57 vertices,
-- 224 edges, `C₄`-free. Slope 224/57 against the 90/31 of V004.
def blocks : SqueezeBench.BoundFn := fun n => 224 * (n / 57)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExC4.Lower.V004.record blocks

end SqueezeBench.ExC4.Lower.V005
