import SqueezeBench.Problems.ExGirthFive.Records.Lower.V002.Def

/-! Record V003 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V003

-- `⌊n/20402⌋` disjoint copies of the point–line incidence graph of the affine plane over `ZMod 101`:
-- 10201 points and 10201 lines `y = a x + b`, so 20402 vertices and 101³ = 1030301 edges, of girth 6.
def blocks : SqueezeBench.BoundFn := fun n => 1030301 * (n / 20402)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V002.record blocks

end SqueezeBench.ExGirthFive.Lower.V003
