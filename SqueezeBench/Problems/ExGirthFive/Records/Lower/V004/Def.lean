import SqueezeBench.Problems.ExGirthFive.Records.Lower.V003.Def

/-! Record V004 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V004

-- `⌊n/2036162⌋` disjoint copies of the point–line incidence graph of the affine plane over `ZMod 1009`:
-- 1018081 points and 1018081 lines `y = a x + b`, so 2036162 vertices and 1009³ = 1027243729 edges, of girth 6.
def blocks : SqueezeBench.BoundFn := fun n => 1027243729 * (n / 2036162)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V003.record blocks

end SqueezeBench.ExGirthFive.Lower.V004
