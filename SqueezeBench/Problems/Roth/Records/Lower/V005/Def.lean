import SqueezeBench.Problems.Roth.Records.Lower.V004.Def

/-! Record V005 for Roth, lower direction, by baseline claude-opus-5: the record function.
The V004 recursion made monotone. `f` is monotone, so a bound proved at `27` holds at every
larger `n`; the V004 recursion forgets that and drops from `11` at `n = 27` to `10` at
`n = 28`, and repeats the dip just above every `3ᵏ`. Folding `f 27 ≥ 11` into every level of
the recursion removes all of them at once. -/

namespace SqueezeBench.Roth.Lower.V005

open SqueezeBench

/-- The V004 recursion with the value at the top of the base window carried upwards. -/
def cntAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n ≤ 27 then SqueezeBench.Roth.Lower.V004.tbl n
      else max (SqueezeBench.Roth.Lower.V004.tbl 27)
        (cntAux fuel ((n + 2) / 3) + cntAux fuel ((n + 1) / 3))

def cnt : BoundFn := fun n => cntAux n n

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Roth.Lower.V004.record cnt

end SqueezeBench.Roth.Lower.V005
