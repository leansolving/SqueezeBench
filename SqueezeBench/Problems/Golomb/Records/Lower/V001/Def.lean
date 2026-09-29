import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V000.Def

/-!
# Golomb lower-bound record V001 — the record function

A sliding-window count. For a window length `u = v + 1` and a threshold `q`, every
`m`-mark ruler of length `L` satisfies

`2 * q * u * m ≤ (L + u) * q * (q + 1) + v * (v + 1)`,

so `L ≥ (2 q u m − v (v+1)) / (q (q+1)) − u`. Taking `q ≈ √m` and `u ≈ q m − q(q+1)/2`
gives roughly `m² − 2 m^{3/2}`, against the seed's `m(m−1)/2`.

`isqrt` is a Newton iteration with structural fuel, so the kernel can evaluate it;
`Nat.sqrt` is defined by well-founded recursion and does not reduce as cheaply.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V001

open SqueezeBench

/-- One Newton step for the integer square root of `n` from the guess `g`. -/
def sqrtStep (n g : ℕ) : ℕ := (g + n / g) / 2

/-- Newton iteration driven by structural fuel. -/
def sqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | k + 1, n, g => if sqrtStep n g < g then sqrtIter k n (sqrtStep n g) else g

/-- Integer square root, kernel-reducible. -/
def isqrt (n : ℕ) : ℕ := if n ≤ 1 then n else sqrtIter n n (n / 2)

/-- The threshold of the tangent-line estimate; any `q ≥ 1` is sound. -/
def qOf (m : ℕ) : ℕ := max 1 (isqrt m)

/-- The window length is `vOf m + 1`; any value is sound. -/
def vOf (m : ℕ) : ℕ := qOf m * m - qOf m * (qOf m + 1) / 2

/-- The window bound, before padding. -/
def wRaw (m : ℕ) : ℕ :=
  (2 * qOf m * (vOf m + 1) * m - vOf m * (vOf m + 1)) / (qOf m * (qOf m + 1)) - (vOf m + 1)

/-- The window bound, pinned below `nMin`. -/
def w : BoundFn := pin nMin wRaw

/-- The record: the seed folded with the window bound. -/
def record : BoundFn := maxWith SqueezeBench.Golomb.Lower.V000.record w

end SqueezeBench.Golomb.Lower.V001
