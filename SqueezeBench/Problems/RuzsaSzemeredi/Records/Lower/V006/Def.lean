import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V005.Def

/-! Record V006 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the record function.
V005's table of base values, extended past `M = 36` by two further explicit 3-AP-free sets, of
size `17` in `[0, 51)` and size `20` in `[0, 69)`, found by a randomised greedy search outside
Lean. Everything else is V005: the same split recursion, consulting the table at every level. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V006

open SqueezeBench

/-- V005's base values with two further entries. -/
def base (m : ℕ) : ℕ :=
  if m < 51 then V005.base m
  else if m < 69 then 17
  else 20

/-- The split recursion of V004, over the extended table. -/
def szAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m =>
      if m ≤ 2 then m
      else max (base m) (szAux fuel ((m + 2) / 3) + szAux fuel ((m + 1) / 3))

/-- The lower bound on the Roth number of `[0, m)`. -/
def sz (m : ℕ) : ℕ := szAux m m

/-- `(2m+1) · sz m` triangles on `6m+3 ≤ n` vertices, `m = ⌊(n-3)/6⌋`. -/
def v : BoundFn := fun n => (2 * V001.blocks n + 1) * sz (V001.blocks n)

def record : SqueezeBench.BoundFn :=
  maxWith SqueezeBench.RuzsaSzemeredi.Lower.V005.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V006
