import SqueezeBench.Problems.Roth.Records.Lower.V005.Def

/-! Record V006 for Roth, lower direction, by baseline claude-opus-5: the record function.
The base window of the last-digit recursion widened from `n ≤ 27` to `n ≤ 56`, using two more
explicit 3-AP-free sets found by a local search. Their prefixes beat the V005 recursion at
`n = 33 … 36` and at `n = 55, 56`, and the recursion is multiplicative in its base, so the gain
propagates to infinitely many larger `n`. -/

namespace SqueezeBench.Roth.Lower.V006

open SqueezeBench

/-- A 3-AP-free subset of `[0, 33)`; its prefixes give `f n ≥ 13` for `n ≥ 33`. -/
def setC : List ℕ := [1, 2, 5, 7, 10, 11, 14, 22, 24, 25, 29, 31, 32]

/-- A 3-AP-free subset of `[0, 55)`; its prefixes give `f n ≥ 17` for `n ≥ 55`. -/
def setD : List ℕ := [2, 3, 5, 6, 12, 13, 15, 16, 31, 36, 38, 39, 43, 44, 51, 53, 54]

/-- The widened base table: the two new sets against the V005 bound. -/
def tbl (n : ℕ) : ℕ :=
  max (max (SqueezeBench.Roth.Lower.V004.below setC n) (SqueezeBench.Roth.Lower.V004.below setD n))
    (SqueezeBench.Roth.Lower.V005.cnt n)

/-- The last-digit recursion over the widened base window, kept monotone as in V005. -/
def cntAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n ≤ 56 then tbl n
      else max (tbl 56) (cntAux fuel ((n + 2) / 3) + cntAux fuel ((n + 1) / 3))

def cnt : BoundFn := fun n => cntAux n n

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Roth.Lower.V005.record cnt

end SqueezeBench.Roth.Lower.V006
