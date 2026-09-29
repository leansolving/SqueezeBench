import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V003.Def

/-! Record V004 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the record function.
V002 and V003 triple a 3-AP-free set by `A ↦ 3A ∪ (3A+1)`, which only uses the power of three
below `m`. The sharper step splits the two halves: from `A ⊆ [0, ⌈m/3⌉)` and `B ⊆ [0, ⌈(m-1)/3⌉)`
the set `3A ∪ (3B+1)` is 3-AP-free inside `[0, m)`, so the Roth number of `[0, m)` is at least
`r(⌈m/3⌉) + r(⌈(m-1)/3⌉)`. Iterated from the base values `r(m) = m` for `m ≤ 2` and `r(m) = 5`
for `9 ≤ m ≤ 11` this counts the whole Szekeres set below `m`, not just the last power of three,
gaining up to a factor two. `⌈m/3⌉ = (m+2)/3` and `⌈(m-1)/3⌉ = (m+1)/3` in `ℕ`. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V004

open SqueezeBench

/-- `szAux fuel m` splits `[0, m)` into its three residue classes mod 3 and keeps two of them. -/
def szAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m =>
      if m ≤ 2 then m
      else if 9 ≤ m ∧ m ≤ 11 then 5
      else szAux fuel ((m + 2) / 3) + szAux fuel ((m + 1) / 3)

/-- The lower bound on the Roth number of `[0, m)`. -/
def sz (m : ℕ) : ℕ := szAux m m

/-- `(2m+1) · sz m` triangles on `6m+3 ≤ n` vertices, `m = ⌊(n-3)/6⌋`. -/
def v : BoundFn := fun n => (2 * V001.blocks n + 1) * sz (V001.blocks n)

def record : SqueezeBench.BoundFn :=
  maxWith SqueezeBench.RuzsaSzemeredi.Lower.V003.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V004
