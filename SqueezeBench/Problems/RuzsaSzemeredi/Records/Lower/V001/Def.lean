import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V000.Def

/-! Record V001 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the record function.
The Ruzsa–Szemerédi tripartite construction: a 3-AP-free set `A ⊆ [0, m)` gives a locally linear
graph on `6m+3` vertices with `(2m+1) · #A` triangles. Here `A = {0, 1}`, whose size is `min m 2`,
so the bound is `(2m+1) · min m 2` with `m = ⌊(n-3)/6⌋`. Folded into V000 with `maxWith`, which
covers the small `n` where the construction is empty. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V001

open SqueezeBench

/-- The largest `m` with `6m+3 ≤ n`. -/
def blocks (n : ℕ) : ℕ := (n - 3) / 6

/-- `(2m+1) · #A` triangles from the 3-AP-free set `A = {0, 1} ∩ [0, m)`. -/
def v : BoundFn := fun n => (2 * blocks n + 1) * min (blocks n) 2

def record : SqueezeBench.BoundFn :=
  maxWith SqueezeBench.RuzsaSzemeredi.Lower.V000.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V001
