import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V001.Def

/-! Record V002 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the record function.
The same tripartite construction as V001, fed with Szekeres' 3-AP-free set instead of `{0, 1}`:
if `A ⊆ [0, m)` is 3-AP-free then so is `3A ∪ (3A+1) ⊆ [0, 3m)`, so the Roth number of `[0, m)`
is at least `2 ^ ⌊log₃ m⌋`. That is computed by a fuel-recursive `szAux`, structural in the
fuel, so the kernel evaluates it in `O(log m)` steps. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V002

open SqueezeBench

/-- `szAux fuel m = 2 ^ ⌊log₃ m⌋` for `1 ≤ m ≤ fuel`, and `0` at `m = 0`. -/
def szAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => if m = 0 then 0 else if m < 3 then 1 else 2 * szAux fuel (m / 3)

/-- The Szekeres lower bound on the Roth number of `[0, m)`. -/
def sz (m : ℕ) : ℕ := szAux m m

/-- `(2m+1) · 2 ^ ⌊log₃ m⌋` triangles on `6m+3 ≤ n` vertices, `m = ⌊(n-3)/6⌋`. -/
def v : BoundFn := fun n => (2 * V001.blocks n + 1) * sz (V001.blocks n)

def record : SqueezeBench.BoundFn :=
  maxWith SqueezeBench.RuzsaSzemeredi.Lower.V001.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V002
