import SqueezeBench.Problems.Roth.Records.Upper.V004.Def

/-! Record V005 for Roth, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V005

-- `⌈n/2⌉` for `n ≥ 8`, `n ≠ 14`: subadditivity over blocks of `8`, `10`, `12`, using the exact
-- values `r₃(8) = 4`, `r₃(10) = 5`, `r₃(12) = 6`. Elsewhere the trivial bound `n`.
def half : SqueezeBench.BoundFn := fun n => if n < 8 ∨ n = 14 then n else (n + 1) / 2

-- Moser's bound: a 3-AP-free `S ⊆ [0, n)` of size `k` has a parity class of size `t ≥ ⌈k/2⌉`
-- whose pairwise sums take at least `3t - 7` values, all with midpoints outside `S`; hence
-- `k + 3 ⌈k/2⌉ ≤ n + 7`, and this is the largest `k` allowed by that inequality.
def moser : SqueezeBench.BoundFn := fun n => max (2 * ((n + 7) / 5)) (2 * ((n + 3) / 5) + 1)

def v : SqueezeBench.BoundFn := fun n => min (half n) (moser n)

-- `r₃(17) ≤ 2 r₃(8) = 8`: a 3-AP-free subset of `[0, 17)` misses an endpoint or the midpoint `8`.
def record : SqueezeBench.BoundFn :=
  SqueezeBench.patch (SqueezeBench.minWith SqueezeBench.Roth.Upper.V004.record v) 17 8

end SqueezeBench.Roth.Upper.V005
