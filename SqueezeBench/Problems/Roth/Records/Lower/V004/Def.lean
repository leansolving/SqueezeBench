import SqueezeBench.Problems.Roth.Records.Lower.V003.Def

/-! Record V004 for Roth, lower direction, by baseline claude-opus-5: the record function.
The last-digit recursion of V002/V003 with the whole window `n ≤ 27` as base case, filled with
the true Roth numbers there. Two explicit 3-AP-free sets supply them: every prefix of a
3-AP-free set is 3-AP-free, so one set certifies a whole row of the table at once. -/

namespace SqueezeBench.Roth.Lower.V004

open SqueezeBench

/-- A 3-AP-free subset of `[0, 26)`; its prefixes give `f 23 ≥ 9`, `f 24 ≥ 10`, `f 26 ≥ 11`. -/
def setA : List ℕ := [0, 1, 4, 6, 10, 15, 17, 18, 22, 23, 25]

/-- A 3-AP-free subset of `[0, 20)`; its prefixes give `f 20 ≥ 9`. -/
def setB : List ℕ := [0, 1, 5, 6, 8, 13, 14, 17, 19]

/-- How many elements of `l` lie below `n`. -/
def below (l : List ℕ) (n : ℕ) : ℕ := (l.filter (fun x => decide (x < n))).length

/-- The base table: the best of the two explicit sets and the V003 bound. -/
def tbl (n : ℕ) : ℕ :=
  max (max (below setA n) (below setB n)) (SqueezeBench.Roth.Lower.V003.cnt n)

/-- The V002 last-digit recursion, bottoming out on the table for `n ≤ 27`. -/
def cntAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n ≤ 27 then tbl n
      else cntAux fuel ((n + 2) / 3) + cntAux fuel ((n + 1) / 3)

def cnt : BoundFn := fun n => cntAux n n

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Roth.Lower.V003.record cnt

end SqueezeBench.Roth.Lower.V004
