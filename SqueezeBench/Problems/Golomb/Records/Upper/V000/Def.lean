import SqueezeBench.Problems.Golomb.Def

/-!
# Golomb upper-bound record V000 — the record function

The smaller of the binary ruler `2^(m-1) - 1` and the quadratic ruler `aᵢ = 2m²·i + i²`
for `i < m`, whose largest mark is `quadLen`. The quadratic ruler is polynomial rather
than exponential but larger for small `m` — the two cross near `m = 13` — so the record
folds both with `minWith`. On top of that, two optimal rulers found by search patch the small
values: `{0, 1, 4, 9, 11}` gives `11` at `m = 5`, and `{0, 1, 4, 10, 12, 17}` gives `17` at `m = 6`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Upper.V000

open SqueezeBench

/-- The largest mark of `quadRuler m`. -/
def quadLen (m : ℕ) : ℕ := 2 * m ^ 2 * (m - 1) + (m - 1) ^ 2

/-- The better of the two constructions at each `m`. -/
def base : BoundFn := minWith (fun m => 2 ^ (m - 1) - 1) quadLen

/-- The seeded upper-bound record: `base`, patched at `m = 5` and `m = 6`. -/
def record : BoundFn := patch (patch base 5 11) 6 17

end SqueezeBench.Golomb.Upper.V000
