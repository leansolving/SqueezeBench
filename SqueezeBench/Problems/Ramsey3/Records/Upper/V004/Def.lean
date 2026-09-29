import SqueezeBench.Problems.Ramsey3.Records.Upper.V003.Def

/-! Record V004 for Ramsey3, upper direction, by trial claude-fable: the record function.

A second level of the deletion argument of V003, in a form that depends only on `n` and
`D = k - 1`. Delete a closed neighbourhood `N[v]` for the vertex `v` whose neighbours have the
largest total degree; the rest has `m' ≥ m := n - 1 - D` vertices and total degree
`σ ≤ X := D (n - 2D)` (the degree sum of `G` is at most `nD`, and `Σ_{w ∈ N(v)} deg w` is at
least the average `Σ_w deg w² / n ≥ (Σ deg)² / n²`). The V003 identity applied inside that
graph, with Cauchy–Schwarz in place of the per-vertex minimisation, gives an independent set of
size at least `q(m', σ/m')` with `q(m, x) = 1 + a (m - 1 - x) - β x (m - 2x)`, and `q` is
decreasing in `x` and increasing in `m` on the relevant ranges, so `α ≥ 1 + q(m, X/m)`. When
that exceeds `D` for `n = N₀`, every graph on `N₀` or more vertices forces (restrict to an
induced subgraph on exactly `N₀` vertices), so no monotonicity in `n` is needed: the record
just checks the certificate `N₀`, in ℕ after clearing the denominators `q(r+1)` and `m²`.

`check D r N₀` is that certificate for the secant point `r`; `v k` returns the least of
`V - 3, V - 2, V - 1` (with `V` the V003 value) certified by some `r < k`, else `V`. -/

namespace SqueezeBench.Ramsey3.Upper.V004

/-- `1 + q(m, X/m) > D` for `m = N₀ - 1 - D`, `X = D (N₀ - 2D)`, `a = A/q'`, `β = B/q'`,
together with the side conditions `2 ≤ D`, `5D + 1 ≤ N₀` and a positive slope `a - βD`. -/
def check (D r N₀ : ℕ) : Bool :=
  let p := (SqueezeBench.Ramsey3.Upper.V002.shearer r).1
  let p' := (SqueezeBench.Ramsey3.Upper.V002.shearer (r + 1)).1
  let q' := (SqueezeBench.Ramsey3.Upper.V002.shearer (r + 1)).2
  let B := p * ((r + 1) * (r + 1) + 1) - p'
  let A := p * ((r + 1) * (r + 1) + 1) + r * B
  let m := N₀ - D - 1
  let X := D * (N₀ - 2 * D)
  decide (2 ≤ D ∧ 5 * D + 1 ≤ N₀ ∧ B * D < A ∧
    (D - 2) * q' * m * m + B * X * m * m + A * m * X < A * m * (m * (m - 1)) + 2 * B * X * X)

/-- Some secant point `r < k` certifies `N₀`. -/
def certified (k N₀ : ℕ) : Bool := (List.range k).any (fun r => check (k - 1) r N₀)

/-- The least certified value among `V - 3, V - 2, V - 1`, else the V003 value `V`. -/
def v : SqueezeBench.BoundFn := fun k =>
  let V := SqueezeBench.Ramsey3.Upper.V003.v k
  if certified k (V - 3) then V - 3
  else if certified k (V - 2) then V - 2
  else if certified k (V - 1) then V - 1
  else V

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Ramsey3.Upper.V003.record v

end SqueezeBench.Ramsey3.Upper.V004
