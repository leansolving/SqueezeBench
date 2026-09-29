import SqueezeBench.Problems.Ramsey3.Records.Upper.V002.Def

/-! Record V003 for Ramsey3, upper direction, by trial claude-fable: the record function.

A second-order refinement of V002. Deleting a closed neighbourhood `N[v]` from a triangle-free
graph on `n` vertices with all degrees at most `D = k - 1` leaves a graph whose average degree
is below `D`; Shearer's theorem (V002) applied to it through the secant line of `f` at a lower
degree `r`, `f(t) ≥ f(r) + (r - t) β` with `β = f(r) - f(r+1)`, and averaged over `v`, gives
`α ≥ 1 + a (n - 1 - D) - β D (n - 2D)` with `a = f(r) + r β`, valid for `n ≥ 4D`. This exceeds
`D` as soon as `n (a - β D) > (D - 1) + a (D + 1) - 2 β D²`, so `max (4D) (⌊X⌋ + 1)` vertices
force, with `X` that quotient. All quantities are kept as naturals over the common denominator
`q(r+1)`; the record takes the best `r < k` and never exceeds V002. -/

namespace SqueezeBench.Ramsey3.Upper.V003

/-- The deletion bound for `D = k - 1` at secant point `r`; `fallback` when the slope
`a - β D` is not positive (the bound is then void). -/
def cand (D r fallback : ℕ) : ℕ :=
  let p := (SqueezeBench.Ramsey3.Upper.V002.shearer r).1
  let p' := (SqueezeBench.Ramsey3.Upper.V002.shearer (r + 1)).1
  let q' := (SqueezeBench.Ramsey3.Upper.V002.shearer (r + 1)).2
  let B := p * ((r + 1) * (r + 1) + 1) - p'
  let A := p * ((r + 1) * (r + 1) + 1) + r * B
  if A ≤ B * D then fallback
  else max (4 * D) (((D - 1) * q' + A * (D + 1) - 2 * B * D * D) / (A - B * D) + 1)

/-- The best secant point `r < k`, starting from the V002 bound. -/
def v : SqueezeBench.BoundFn := fun k =>
  (List.range k).foldl (fun acc r => min acc (cand (k - 1) r (SqueezeBench.Ramsey3.Upper.V002.v k)))
    (SqueezeBench.Ramsey3.Upper.V002.v k)

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Ramsey3.Upper.V002.record v

end SqueezeBench.Ramsey3.Upper.V003
