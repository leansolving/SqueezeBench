import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V005.Def

-- Record V006 for Ramsey3, lower direction, by trial claude-fable.
--
-- Same recursion as V005 (the Chung–Cleve–Dagum fibration, `g m = max (base m) (6·g⌊m/4⌋)`),
-- with a better base. Disjoint unions add vertex counts and independence numbers, so the base
-- is a knapsack over certified pieces: the Kalbfleisch circulant `C₃₅(±1,±7,±11,±16)`
-- (35 vertices, independence number 8, the extremal graph for `R(3,9) = 36`), `C₁₃(±1,±5)`
-- (13, 4), the Wagner graph `C₈(±1,4)` (8, 3), `C₅` (5, 2) and an edge (2, 1).
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V006

open SqueezeBench

-- Vertices for independence number `r` from the small pieces: `13⌊r/4⌋` plus `0, 2, 5, 8`
-- for the remainder `0, 1, 2, 3`.
def rem (r : ℕ) : ℕ := 13 * (r / 4) + (if r % 4 = 0 then 0 else 3 * (r % 4) - 1)

-- As many copies of the 35-vertex graph as fit, and the best small piece for the rest.
def base (m : ℕ) : ℕ := 35 * (m / 8) + rem (m % 8)

-- Iterate the fibration, as in V005.
def gAux : ℕ → ℕ → ℕ
  | 0, m => base m
  | fuel + 1, m => if m < 4 then base m else max (base m) (gAux fuel (m / 4) * 6)

def g (m : ℕ) : ℕ := gAux m m

-- The new bound, padded with `0` below `nMin`.
def v : SqueezeBench.BoundFn := pin nMin (fun k => g (k - 1) + 1)

-- Folded into the previous record, which is larger at `k = 3`.
def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey3.Lower.V005.record v

end SqueezeBench.Ramsey3.Lower.V006
