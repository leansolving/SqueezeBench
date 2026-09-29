import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V006.Def

/-! Record V007 for RuzsaSzemeredi, lower direction, by trial claude-fable: the record function.
Two constructions from **cap sets** (3-AP-free subsets of `F₃^k`), which are much larger than the
integer 3-AP-free sets of V001–V006: the Hill cap gives `112` points in `F₃^6` where the digit
construction gives `2^6 = 64`, and products of Hill blocks give `112^(k/6)` in `F₃^k`.

* `tripAt n k`: the tripartite Ruzsa–Szemerédi construction over the group `F₃^k × Z_{2m+1}` with
  the product of a cap of size `capB k` and V006's integer 3-AP-free set of size `sz m`:
  `3^k · (2m+1) · capB k · sz m` triangles on `3 · 3^k · (2m+1) ≤ n` vertices.
* `cayAt k`: the Cayley graph of a *symmetric* cap `C = -C ∌ 0` of size `symB k` in `F₃^k`, whose
  triangles are the affine lines `{x, x+a, x-a}`, `a ∈ C`: `3^k · symB k / 6` triangles on `3^k`
  vertices (for `k = 6` this is the Games graph).

`record n` is the maximum of V006 and of both constructions over all admissible `k`. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V007

open SqueezeBench

/-- Sizes of the explicit caps in `F₃^r` used for `r ≤ 5`: `1, 2, 4, 9, 20, 45`. -/
def capr (r : ℕ) : ℕ :=
  if r = 0 then 1 else if r = 1 then 2 else if r = 2 then 4 else if r = 3 then 9
  else if r = 4 then 20 else 45

/-- Sizes of the explicit symmetric caps in `F₃^r` used for `r ≤ 5`: `1, 2, 4, 8, 20, 40`. -/
def symr (r : ℕ) : ℕ :=
  if r = 0 then 1 else if r = 1 then 2 else if r = 2 then 4 else if r = 3 then 8
  else if r = 4 then 20 else 40

/-- A cap in `F₃^k`: `k / 6` Hill blocks of `112` points and one small block. -/
def capB (k : ℕ) : ℕ := 112 ^ (k / 6) * capr (k % 6)

/-- A symmetric cap in `F₃^k` of the same shape. -/
def symB (k : ℕ) : ℕ := 112 ^ (k / 6) * symr (k % 6)

/-- The tripartite construction over `F₃^k × Z_{2m+1}`, `m` the largest with
`3 · 3^k · (2m+1) ≤ n`. -/
def tripAt (n k : ℕ) : ℕ :=
  let q := n / (3 * 3 ^ k)
  if q = 0 then 0 else
    let m := (q - 1) / 2
    3 ^ k * (2 * m + 1) * (capB k * V006.sz m)

/-- The best tripartite bound over `k ≤ fuel`. -/
def tripAux : ℕ → ℕ → ℕ
  | 0, n => tripAt n 0
  | k + 1, n => max (tripAt n (k + 1)) (tripAux k n)

/-- The Cayley graph of a symmetric cap of size `symB k` in `F₃^k`: `3^k · symB k / 6` triangles
on `3^k` vertices. -/
def cayAt (k : ℕ) : ℕ := 3 ^ k * symB k / 6

/-- The best Cayley bound over `1 ≤ k ≤ fuel` with `3^k ≤ n`. -/
def cayAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if 3 ^ (k + 1) ≤ n then max (cayAt (k + 1)) (cayAux k n) else cayAux k n

/-- `⌊log₃ n⌋` by fuel recursion, so that the kernel evaluates it in `O(log n)` steps. -/
def log3Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n < 3 then 0 else log3Aux fuel (n / 3) + 1

/-- `⌊log₃ n⌋`. -/
def log3 (n : ℕ) : ℕ := log3Aux n n

/-- The better of the two cap constructions at `n`. -/
def v : SqueezeBench.BoundFn := fun n => max (tripAux (log3 n) n) (cayAux (log3 n) n)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.RuzsaSzemeredi.Lower.V006.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V007
