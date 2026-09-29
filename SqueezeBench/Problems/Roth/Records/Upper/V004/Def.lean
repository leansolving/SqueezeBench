import SqueezeBench.Problems.Roth.Records.Upper.V003.Def

/-! Record V004 for Roth, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V004

-- Subadditivity applied to the exact value `r₃(8) = 4`: writing `n = 8 * q + t` with `t < 8`,
-- `r₃(n) ≤ 4 * q + r₃(t)`, and the V003 record bounds the remainder. It is one less than V003
-- at every `n ≡ 0, 1 (mod 8)`, and equal to it at the other residues.
def v : SqueezeBench.BoundFn :=
  fun n => 4 * (n / 8) + SqueezeBench.Roth.Upper.V003.record (n % 8)

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Roth.Upper.V003.record v

end SqueezeBench.Roth.Upper.V004
