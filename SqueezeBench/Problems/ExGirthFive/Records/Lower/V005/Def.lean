import SqueezeBench.Problems.ExGirthFive.Records.Lower.V004.Def

/-! Record V005 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V005

-- `⌊n/200280098⌋` disjoint copies of the point–line incidence graph of the affine plane over `ZMod 10007`:
-- 100140049 points and 100140049 lines `y = a x + b`, so 200280098 vertices and 10007³ = 1002101470343 edges, of girth 6.
def blocks : SqueezeBench.BoundFn := fun n => 1002101470343 * (n / 200280098)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V004.record blocks

end SqueezeBench.ExGirthFive.Lower.V005
