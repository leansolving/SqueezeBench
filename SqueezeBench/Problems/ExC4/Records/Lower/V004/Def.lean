import SqueezeBench.Problems.ExC4.Records.Lower.V003.Def

/-! Record V004 for ExC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExC4/Lower/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExC4.Lower.V004

-- `⌊n/31⌋` disjoint copies of the Erdős–Rényi polarity graph of PG(2,5): 31 vertices,
-- 90 edges, `C₄`-free. Slope 90/31 against the 50/21 of V003.
def blocks : SqueezeBench.BoundFn := fun n => 90 * (n / 31)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExC4.Lower.V003.record blocks

end SqueezeBench.ExC4.Lower.V004
