import SqueezeBench.Problems.Roth.Records.Upper.V002.Def

/-! Record V003 for Roth, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Roth/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.Roth.Upper.V003

-- `1, 2, 2, 2, 3, 4, 4, 4, 5, …`: the V002 bound `⌊(n+3)/2⌋` sharpened by one at every
-- `n ≡ 3 (mod 4)`, where the count of V002 cannot be met by an integer split of the two
-- parity classes. Equal to `2 * (n / 4) + 1` for `n ≡ 0 (mod 4)` and `2 * (n / 4) + 2`
-- otherwise, written with divisions so that the kernel evaluates it in `ℕ`.
def v : SqueezeBench.BoundFn := fun n => (n + 2) / 2 + (n + 3) / 4 - (n + 2) / 4

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Roth.Upper.V002.record v

end SqueezeBench.Roth.Upper.V003
