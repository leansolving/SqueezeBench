import SqueezeBench.Problems.ExGirthFive.Records.Lower.V001.Def

/-! Record V002 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V002

-- `⌊n/242⌋` disjoint copies of the point–line incidence graph of the affine plane over `ZMod 11`:
-- 121 points and 121 lines `y = a x + b`, so 242 vertices and 11³ = 1331 edges, of girth 6.
def blocks : SqueezeBench.BoundFn := fun n => 1331 * (n / 242)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V001.record blocks

end SqueezeBench.ExGirthFive.Lower.V002
