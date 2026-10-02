import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V008.Def

/-! Record V009 for RuzsaSzemeredi, lower direction, by Pablo Manrique: the record function.
Two operations on locally linear graphs, and two small graphs that the group constructions of
V001–V008 do not reach.

* **Tensor product.** If `G` and `H` are locally linear, so is `G × H` (`(x, y) ~ (x', y')` iff
  `x ~ x'` and `y ~ y'`): the common neighbours of an edge are the pairs of common neighbours of
  its projections, and every pair of triangles gives `3! = 6` triangles of the product. Hence
  `f (a · b) ≥ 6 · f a · f b`.
* **Disjoint union.** `f (a + b) ≥ f a + f b`.
* **`KG(6,2)`**, the collinearity graph of the generalized quadrangle `GQ(2,2)`: `15` vertices,
  `15` triangles (V008 has `10` at `n = 15`); and the collinearity graph of **`GQ(2,4)`** (the
  intersection graph of the 27 lines on a cubic surface, triangles = tritangent planes): `27`
  vertices, `45` triangles (V008 has `36`). Upper V008 is `15` and `45` at these `n`.

`tAux` multiplies V008 by the two small graphs recursively, `f n ≥ 6 · 15 · f ⌊n/15⌋` and
`f n ≥ 6 · 45 · f ⌊n/27⌋` (the factor alone, `15` or `45`, when the cofactor is too small to carry a
triangle); `sAux` then splits `n` as `(n - n % 3^k) + n % 3^k` and adds the two bounds, which
fills the flat stretches of the step function. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V009

open SqueezeBench

/-- The best of V008 and of the products with `KG(6,2)` (`15` vertices, `15` triangles) and
`GQ(2,4)` (`27` vertices, `45` triangles), by fuel recursion on `n`. -/
def tAux : ℕ → ℕ → ℕ
  | 0, n => V008.record n
  | fuel + 1, n =>
      if n < 15 then V008.record n
      else max (V008.record n)
        (max (max 15 (90 * tAux fuel (n / 15)))
          (if n < 27 then 0 else max 45 (270 * tAux fuel (n / 27))))

/-- The tensor-product bound. -/
def tb (n : ℕ) : ℕ := tAux n n

/-- The best split `n = (n - n % 3^j) + n % 3^j` over `1 ≤ j ≤ k`, or `tb n`. -/
def sAux : ℕ → ℕ → ℕ
  | 0, n => tb n
  | k + 1, n => max (tb (n - n % 3 ^ (k + 1)) + tb (n % 3 ^ (k + 1))) (sAux k n)

def record : SqueezeBench.BoundFn := fun n => sAux (V007.log3 n) n

end SqueezeBench.RuzsaSzemeredi.Lower.V009
