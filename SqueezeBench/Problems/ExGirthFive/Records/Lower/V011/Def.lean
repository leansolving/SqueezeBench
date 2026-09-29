import SqueezeBench.Problems.ExGirthFive.Records.Lower.V010.Def

/-! Record V011 for ExGirthFive, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V011.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V011

-- `tab[n]` is the number of edges of the Hoffman–Singleton graph induced on the first `n` vertices
-- of a fixed ordering of its 50 vertices (pentagon `0`, pentagram `0`, pentagon `1`, …; see
-- `rank` in `Proof.lean`). `tab[10] = 15` is the Petersen graph, `tab[40] = 120` the `(6,5)`-cage,
-- `tab[50] = 175` the Hoffman–Singleton graph itself; the values agree with `f` for `n ≤ 12` and
-- `34 ≤ n ≤ 50`.
def tab : List ℕ := [0, 0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 20, 22, 25, 27, 29, 32, 36, 40, 42,
  45, 48, 51, 55, 58, 62, 66, 70, 75, 78, 82, 86, 90, 95, 99, 104, 109, 114, 120, 124, 129, 134,
  139, 145, 150, 156, 162, 168, 175]

-- The Hoffman–Singleton graph and its prefixes; `175` for every `n ≥ 50` (isolated vertices).
def hs : SqueezeBench.BoundFn := fun n => if 50 ≤ n then 175 else tab.getD n 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V010.record hs

end SqueezeBench.ExGirthFive.Lower.V011
