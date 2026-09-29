import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V004.Def

/-! Record V005 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the record function.
V004's split recursion `r(m) ≥ r(⌈m/3⌉) + r(⌈(m-1)/3⌉)` bottoms out in the single base value
`r(9) ≥ 5`. Here it is bottomed out in a whole table of base values, each carried by an explicit
3-AP-free subset of `[0, M)` exhibited in `Proof.lean`, and the table is consulted at *every* level
of the recursion, not only at the bottom: `sz m = max (base m) (sz ⌈m/3⌉ + sz ⌈(m-1)/3⌉)`. The
table is the exact Roth number of `[0, M)` at the thresholds `M = 9, 11, 20, 24, 26, 30, 32, 36`,
which is where it first exceeds what the split recursion alone produces. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V005

open SqueezeBench

/-- Base values: `base m` is a size that an explicit 3-AP-free subset of `[0, m)` attains. -/
def base (m : ℕ) : ℕ :=
  if m < 9 then 0
  else if m < 11 then 5
  else if m < 20 then 6
  else if m < 24 then 9
  else if m < 26 then 10
  else if m < 30 then 11
  else if m < 32 then 12
  else if m < 36 then 13
  else 14

/-- The split recursion of V004, taking the best of the table and the split at every level. -/
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
  maxWith SqueezeBench.RuzsaSzemeredi.Lower.V004.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V005
