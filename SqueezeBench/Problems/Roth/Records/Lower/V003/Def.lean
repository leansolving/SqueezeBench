import SqueezeBench.Problems.Roth.Records.Lower.V002.Def

/-! Record V003 for Roth, lower direction, by baseline claude-opus-5: the record function.
The V002 recursion with a better base case. `{0,1,3,7,8}` is 3-AP-free, so `f 9 ≥ 5` while the
base-3 digit set gives only `4`; feeding that single extra point into the last-digit recursion
multiplies the bound by `5/4` at every `n ≥ 27`. -/

namespace SqueezeBench.Roth.Lower.V003

open SqueezeBench

/-- The last-digit recursion of V002, bottoming out on `n ≤ 9` with the exact Roth numbers
there — `f 9 = 5` is the first value the digit construction misses. -/
def cntAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n ≤ 8 then SqueezeBench.Roth.Lower.V002.cnt n
      else if n = 9 then 5
      else cntAux fuel ((n + 2) / 3) + cntAux fuel ((n + 1) / 3)

def cnt : BoundFn := fun n => cntAux n n

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Roth.Lower.V002.record cnt

end SqueezeBench.Roth.Lower.V003
