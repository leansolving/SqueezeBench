import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V007.Def

/-! Record V008 for RuzsaSzemeredi, lower direction, by trial claude-fable: the record function.
V007's tripartite construction over `F₃^k × Z_N` takes its `Z_N` factor from V006's integer
3-AP-free sets: `Z_{2m+1} ⊇ [0, m)` with `sz m` elements. But 3-AP-free subsets of the cyclic
group `Z_N` itself (no `a + c ≡ 2b (mod N)` with `a ≠ b`) can be larger — `{0, 1, 3}` in `Z_7`
against `sz 3 = 2` — and here a table `zt` of sizes of such sets for odd `N ≤ 99`, each carried
by an explicit set exhibited in `Proof.lean`, replaces `sz` wherever it is better (`zr`). The
`Z_N` factor is then chosen among the odd `N` up to the available room, not just the largest one
(`zbest`). Everything else is V007 (its Cayley graphs and its caps `capB`), and the record is the
maximum with V007. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V008

open SqueezeBench

/-- Sizes of explicit 3-AP-free subsets of `Z_N` for the odd `N ≤ 99` where they exceed V006's
`sz ((N-1)/2)` (exact maxima for `N ≤ 61`); `0` elsewhere. -/
def zt (N : ℕ) : ℕ :=
  if N = 1 then 1 else if N = 3 then 2 else if N = 7 then 3 else if N = 9 then 4 else if N = 17 then 5 else if N = 19 then 6 else if N = 21 then 6 else if N = 25 then 7 else if N = 27 then 8 else if N = 35 then 9 else if N = 37 then 10 else if N = 39 then 10 else if N = 45 then 10 else if N = 47 then 10 else if N = 51 then 11 else if N = 57 then 12 else if N = 59 then 12 else if N = 61 then 13 else if N = 63 then 13 else if N = 65 then 14 else if N = 69 then 14 else if N = 71 then 14 else if N = 79 then 15 else if N = 81 then 16 else if N = 85 then 17 else if N = 93 then 17 else if N = 95 then 17 else if N = 97 then 17 else if N = 99 then 17 else 0

/-- The lower bound on the size of a 3-AP-free subset of `Z_N`, `N` odd. -/
def zr (N : ℕ) : ℕ := max (zt N) (V006.sz ((N - 1) / 2))

/-- `max` of `(2m'+1) · zr (2m'+1)` over `m' ≤ m` (fuel-bounded, descending). -/
def tbAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => max ((2 * m + 1) * zr (2 * m + 1)) (tbAux fuel (m - 1))

/-- The best `N · zr N` over odd `N ≤ q`: the largest odd `N ≤ q`, or a table entry. -/
def zbest (q : ℕ) : ℕ :=
  let m := (q - 1) / 2
  max ((2 * m + 1) * zr (2 * m + 1)) (tbAux 50 (min m 49))

/-- The tripartite construction over `F₃^k × Z_N`, `3 · 3^k · N ≤ n`, with the best odd `N`. -/
def tripAt (n k : ℕ) : ℕ :=
  let q := n / (3 * 3 ^ k)
  if q = 0 then 0 else 3 ^ k * V007.capB k * zbest q

/-- The best tripartite bound over `k ≤ fuel`. -/
def tripAux : ℕ → ℕ → ℕ
  | 0, n => tripAt n 0
  | k + 1, n => max (tripAt n (k + 1)) (tripAux k n)

/-- The new tripartite bound. -/
def v : SqueezeBench.BoundFn := fun n => tripAux (V007.log3 n) n

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.RuzsaSzemeredi.Lower.V007.record v

end SqueezeBench.RuzsaSzemeredi.Lower.V008
