import SqueezeBench.Problems.Roth.Records.Upper.V005.Def

/-! Record V006 for Roth, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V006

-- Moser's second bound, `4n/11 + O(1)`: a 3-AP-free `t`-set has at least `(7t - 20)/2` distinct
-- pairwise sums (deleting its two smallest elements kills seven of them), so the size `k` of a
-- 3-AP-free subset of `[0, n)` satisfies `2k + 7⌈k/2⌉ ≤ 2n + 20`; this is its largest solution.
def v : SqueezeBench.BoundFn :=
  fun n => max (2 * ((2 * n + 20) / 11)) (2 * ((2 * n + 11) / 11) + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Roth.Upper.V005.record v

end SqueezeBench.Roth.Upper.V006
