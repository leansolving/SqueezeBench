import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V004.Def

/-!
# Golomb lower-bound record V005 — the record function

V004's boundary correction with **three** nested blocks instead of two: the next term of the
Riemann sum of the slack profile `slack q κ(s)`, `κ(s) ≈ √(2s)`, whose exact integral is
`q⁴/12` per end. With `A_i = K_i(K_i+1)/2` and telescoping weights
`W_i = slack q K_i − slack q K_{i+1}` (`W₃ = slack q K₃`), the gain is
`2 (A₁ W₁ + A₂ W₂ + A₃ W₃)`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V005

open SqueezeBench

/-- The three-block boundary gain, with V004's `slack` and V003's `blockLen`. -/
def gain (q K₁ K₂ K₃ : ℕ) : ℕ :=
  2 * (SqueezeBench.Golomb.Lower.V003.blockLen K₁
        * (SqueezeBench.Golomb.Lower.V004.slack q K₁ - SqueezeBench.Golomb.Lower.V004.slack q K₂)
      + SqueezeBench.Golomb.Lower.V003.blockLen K₂
        * (SqueezeBench.Golomb.Lower.V004.slack q K₂ - SqueezeBench.Golomb.Lower.V004.slack q K₃)
      + SqueezeBench.Golomb.Lower.V003.blockLen K₃ * SqueezeBench.Golomb.Lower.V004.slack q K₃)

/-- The master inequality with the three-block boundary gain, solved for `L`. -/
def gbnd (m q u K₁ K₂ K₃ : ℕ) : ℕ :=
  if 0 < q ∧ 0 < u ∧ K₁ < K₂ ∧ K₂ < K₃ ∧
      2 * SqueezeBench.Golomb.Lower.V003.blockLen K₃ ≤ SqueezeBench.Golomb.Lower.V002.bnd m q u then
    (2 * q * u * m + gain q K₁ K₂ K₃ - (u - 1) * u) / (q * (q + 1)) - u
  else 0

/-- The caps around `q/4`, `q/2`, `7q/10`. -/
def bestK (m q u : ℕ) : ℕ :=
  max (max (gbnd m q u (q / 4) (q / 2) (7 * q / 10))
        (gbnd m q u (q / 4) (q / 2) (7 * q / 10 + 1)))
    (max (gbnd m q u (q / 4 + 1) (q / 2) (7 * q / 10))
      (max (gbnd m q u (q / 4) (q / 2 + 1) (7 * q / 10))
        (gbnd m q u (q / 4 + 1) (q / 2 + 1) (7 * q / 10 + 1))))

/-- The two window lengths around V002's maximiser. -/
def bestU (m q : ℕ) : ℕ :=
  max (bestK m q (SqueezeBench.Golomb.Lower.V002.uOf m q + 1))
    (bestK m q (SqueezeBench.Golomb.Lower.V002.uOf m q + 2))

/-- The best over the thresholds around `⌊√m⌋`. -/
def wRaw (m : ℕ) : ℕ :=
  max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m))
    (max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m + 1))
      (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m - 1)))

/-- The three-block boundary bound, pinned below `nMin`. -/
def w : BoundFn := pin nMin wRaw

/-- The record: V004 folded with the three-block boundary bound. -/
def record : BoundFn := maxWith SqueezeBench.Golomb.Lower.V004.record w

end SqueezeBench.Golomb.Lower.V005
