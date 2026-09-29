import SqueezeBench.Problems.Roth.Records.Upper.V006.Def

/-! Record V007 for Roth, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V007

-- The V006 count with its true base cases: a 3-AP-free `t`-set has at least `(7t - 18)/2`
-- distinct pairwise sums (exactly `9` and `12` for `t = 5, 6`), so a 3-AP-free `k`-subset of
-- `[0, n)` satisfies `2k + 7⌈k/2⌉ ≤ 2n + 18`; this is the largest such `k`.
def v : SqueezeBench.BoundFn :=
  fun n => max (2 * ((2 * n + 18) / 11)) (2 * ((2 * n + 9) / 11) + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Roth.Upper.V006.record v

end SqueezeBench.Roth.Upper.V007
