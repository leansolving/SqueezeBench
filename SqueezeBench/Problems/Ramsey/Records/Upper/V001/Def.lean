import SqueezeBench.Problems.Ramsey.Records.Upper.V000.Def

/-! Record V001 for Ramsey, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The Erdős–Szekeres recursion `R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t)` with the parity saving:
when both summands are even the bound drops by one. Running the sharpened recursion over
the whole off-diagonal table beats the plain binomial bound `C(2n-2, n-1)` at every
`n ≥ 4`.

`dRow k i` is the entry of the table at `R(i, k + 2 - i)`, so the antidiagonals of the
table are the "rows" here and the recursion is Pascal's rule with `stepVal` in place of
addition. Natural subtraction keeps the right-hand boundary at `0` by itself. -/

namespace SqueezeBench.Ramsey.Upper.V001

open SqueezeBench

/-- One Erdős–Szekeres step: `a + b`, less one when both summands are even. -/
def stepVal (a b : ℕ) : ℕ := if a % 2 = 0 ∧ b % 2 = 0 then a + b - 1 else a + b

/-- `dRow k i` bounds the off-diagonal Ramsey number `R(i, k + 2 - i)`. -/
def dRow : ℕ → ℕ → ℕ
  | 0 => fun i => if i = 1 then 1 else 0
  | k + 1 => fun i => if i = 0 then 0 else stepVal (dRow k (i - 1)) (dRow k i)

def record : SqueezeBench.BoundFn := fun n => dRow (2 * n - 2) n

end SqueezeBench.Ramsey.Upper.V001
