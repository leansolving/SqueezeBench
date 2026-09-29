import SqueezeBench.Problems.ExGirthFive.Records.Upper.V004.Def

/-! Record V005 for ExGirthFive, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Upper/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Upper.V005

-- The residue `ρ = n - 1 - q²` of `n - 1` above the square `q²` (truncated at `0`).
def rho (n q : ℕ) : ℕ := n - 1 - q * q

-- The denominator `D = ρ(2q - 1) - 1` of the bound; it is `0` exactly when `ρ = 0` or `q ≤ 1`.
def den (n q : ℕ) : ℕ := rho n q * (2 * q - 1) - 1

-- Summing the per-vertex count `∑_{u ~ x} d(u) ≤ n - 1` over *every* vertex `x` of degree
-- `≥ q + 1` at once: each such vertex needs at least `q - ρ` units of degree shortfall below
-- `q` among its neighbours, a vertex of degree `q - s` can supply at most `s(q - s)` of them,
-- and it returns `2s` to the chord sum of V002. Together `D·2m ≤ D·nq + nρ(ρ - 1)`.
-- When `D = 0` the bound falls back to `C(n, 2)`.
def bnd (n q : ℕ) : ℕ :=
  if den n q = 0 then n * (n - 1) / 2
  else (den n q * (n * q) + n * rho n q * (rho n q - 1)) / (2 * den n q)

-- Only `q = ⌊√(n - 1)⌋` can gain: at `q + 1` the residue is `0`, at `q - 1` it exceeds `q`.
def v : SqueezeBench.BoundFn := fun n => bnd n (Nat.sqrt (n - 1))

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExGirthFive.Upper.V004.record v

end SqueezeBench.ExGirthFive.Upper.V005
