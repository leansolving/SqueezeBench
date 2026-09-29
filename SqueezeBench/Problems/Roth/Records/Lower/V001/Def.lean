import SqueezeBench.Problems.Roth.Records.Lower.V000.Def

/-! Record V001 for Roth, lower direction, by baseline claude-opus-5: the record function.
The Szekeres construction: from a 3-AP-free `A ⊆ [0, m)` the set `3A ∪ (3A+1)` is 3-AP-free in
`[0, 3m)`, so `f (3 * m) ≥ 2 * f m`. Iterating from `f n ≥ 1` gives `2 ^ ⌊log₃ n⌋`, computed
here by a structurally recursive halving so that the kernel can evaluate it. Folded into the
previous record with `maxWith`, which covers `n = 2`, where `min n 2` is the better of the two. -/

namespace SqueezeBench.Roth.Lower.V001

open SqueezeBench

/-- `szAux fuel n = 2 ^ ⌊log₃ n⌋` once `fuel ≥ n`; structural in `fuel`, so the kernel
evaluates it in `O(log n)` steps. -/
def szAux : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, n => if n < 3 then 1 else 2 * szAux fuel (n / 3)

/-- The Szekeres bound `2 ^ ⌊log₃ n⌋`. -/
def szekeres : BoundFn := fun n => szAux n n

def record : SqueezeBench.BoundFn :=
  maxWith SqueezeBench.Roth.Lower.V000.record (pin SqueezeBench.Roth.nMin szekeres)

end SqueezeBench.Roth.Lower.V001
