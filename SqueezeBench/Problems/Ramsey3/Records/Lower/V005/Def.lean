import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V004.Def

-- Record V005 for Ramsey3, lower direction, by trial claude-fable.
--
-- A super-linear bound: `R(3,k) ≥ g(k-1) + 1` where `g` iterates the Chung–Cleve–Dagum
-- fibration. If `G` is triangle-free with independence number at most `m`, the graph on
-- `V(G) × Z₆` that joins `(u,i)` to `(v,j)` when `u ~ v` and `i, j` are at cyclic distance at
-- most `1`, and joins `(u,i)` to `(u,i+3)`, is triangle-free with independence number at most
-- `4m` on six times as many vertices. Applied `r` times to a base graph with parameters
-- `(n₀, m₀)` this gives `(6^r n₀, 4^r m₀)`, i.e. `R(3,k) = Ω(k^{log 6 / log 4})`.
-- The base is the best certified fixed graph: the unbalanced blow-ups of `C₁₃(±1,±5)` (V004)
-- and of `C₅` (V001). Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V005

open SqueezeBench

-- Vertices of the best certified fixed graph with independence number at most `m`.
def base (m : ℕ) : ℕ := max (13 * (m / 4) + 2 * (m % 4)) (5 * m / 2)

-- Iterate the fibration: `m` vertices of independence go to `m / 4` on the base graph and
-- the vertex count comes back multiplied by `6`. `fuel` bounds the depth; below `4` there is
-- nothing left to divide.
def gAux : ℕ → ℕ → ℕ
  | 0, m => base m
  | fuel + 1, m => if m < 4 then base m else max (base m) (gAux fuel (m / 4) * 6)

-- The largest certified vertex count for independence number at most `m`.
def g (m : ℕ) : ℕ := gAux m m

-- The new bound, padded with `0` below `nMin`.
def v : SqueezeBench.BoundFn := pin nMin (fun k => g (k - 1) + 1)

-- Folded into the previous record, which is larger at `k = 3` and `k = 4`.
def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey3.Lower.V004.record v

end SqueezeBench.Ramsey3.Lower.V005
