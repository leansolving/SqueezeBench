import SqueezeBench.Problems.Golomb.Records.Upper.V000.Def

/-!
# Golomb upper-bound record V001 — the record function

The Erdős–Turán ruler `aₖ = 2pk + (k² mod p)` for `k < m`, laid out modulo a prime `p`
with `m < p ≤ 2m` supplied by Bertrand's postulate. Its largest mark is
`2p(m-1) + ((m-1)² mod p) ≤ 4m² - 2m - 1`, so the bound is quadratic in `m` where the
previous record was exponential (binary ruler) or cubic (`aᵢ = 2m²i + i²`).

`etLen` is folded into the previous record with `minWith`, since the binary ruler is still
smaller for `m ≤ 9`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Upper.V001

open SqueezeBench

/-- The Bertrand bound on the length of the `m`-mark Erdős–Turán ruler.
Natural subtraction makes this `0` at `m = 0` and `1` at `m = 1`, both still valid. -/
def etLen (m : ℕ) : ℕ := 4 * m ^ 2 - 2 * m - 1

/-- The previous record folded with the Erdős–Turán bound. -/
def record : SqueezeBench.BoundFn := minWith SqueezeBench.Golomb.Upper.V000.record etLen

end SqueezeBench.Golomb.Upper.V001
