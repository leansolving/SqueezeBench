import SqueezeBench.Problems.Roth.Records.Lower.V001.Def

/-! Record V002 for Roth, lower direction, by baseline claude-opus-5: the record function.
The Szekeres set below an arbitrary bound: the integers in `[0, n)` whose base-3 digits avoid `2`.
Splitting on the last digit gives `c n = c ⌈n/3⌉ + c ⌈(n-1)/3⌉`, which is exactly the count of
that set, and `2 ^ ⌊log₃ n⌋` only at the powers of 3. -/

namespace SqueezeBench.Roth.Lower.V002

open SqueezeBench

/-- `cntAux fuel n` counts the integers below `n` whose base-3 digits are `0` or `1`, once
`fuel ≥ n`. Structural in `fuel`, so the kernel evaluates it; the recursion depth is `log₃ n`. -/
def cntAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n ≤ 2 then n else cntAux fuel ((n + 2) / 3) + cntAux fuel ((n + 1) / 3)

/-- The number of base-3 digit-`2`-free integers below `n`. -/
def cnt : BoundFn := fun n => cntAux n n

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Roth.Lower.V001.record cnt

end SqueezeBench.Roth.Lower.V002
