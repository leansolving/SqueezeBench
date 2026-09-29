import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V002.Def

/-! Record V003 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the record function.
V002's tripling recursion with a better base case. `{0, 1, 3, 7, 8} ⊆ [0, 9)` is 3-AP-free, so the
Roth number of `[0, 9)` is at least `5`, while the base-3 digit construction gives only `4`.
Bottoming the recursion out there multiplies the bound by `5/4` at every `m ≥ 27`. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V003

open SqueezeBench

/-- `szAux fuel m` is `2 ^ ⌊log₃ (m/9)⌋ · 5` once `m ≥ 9`, with the exact small values below. -/
def szAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m =>
      if m = 0 then 0
      else if m < 3 then 1
      else if m < 9 then 2
      else if m < 27 then 5
      else 2 * szAux fuel (m / 3)

/-- The improved lower bound on the Roth number of `[0, m)`. -/
def sz (m : ℕ) : ℕ := szAux m m

/-- `(2m+1) · sz m` triangles on `6m+3 ≤ n` vertices, `m = ⌊(n-3)/6⌋`. -/
def v : BoundFn := fun n => (2 * V001.blocks n + 1) * sz (V001.blocks n)

def record : SqueezeBench.BoundFn :=
  maxWith SqueezeBench.RuzsaSzemeredi.Lower.V002.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V003
