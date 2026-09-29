import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V003.Def

/-!
# Golomb lower-bound record V004 — the record function

V003 harvested the boundary slack of the sliding window with **one** block of
`A = K(K+1)/2` windows at each end and one cap `K`. The true slack profile of the window
ending at `s` is `(q − κ(s))(q − κ(s) + 1)` with `κ(s) ≈ √(2s)`; V004 approximates it by
**two nested blocks** `A₁ ≤ A₂` with caps `K₁ < K₂` and telescoping weights

`W₁ = slack K₁ − slack K₂`,  `W₂ = slack K₂`,  `slack K = (q − K)(q − K + 1)`,

so that the weight assigned to a window is `slack K₁` on the innermost block and
`slack K₂` on the outer one — in both cases exactly the slack available there. The gain is
`2 (A₁ W₁ + A₂ W₂)`, about `q⁴/18` against V003's `q⁴/32`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V004

open SqueezeBench

/-- The slack of the integrality step on a window holding at most `K` marks. -/
def slack (q K : ℕ) : ℕ := (q - K) * (q - K + 1)

/-- The two-block boundary gain. -/
def gain (q K₁ K₂ : ℕ) : ℕ :=
  2 * (SqueezeBench.Golomb.Lower.V003.blockLen K₁ * (slack q K₁ - slack q K₂)
    + SqueezeBench.Golomb.Lower.V003.blockLen K₂ * slack q K₂)

/-- The master inequality with the two-block boundary gain, solved for `L`. -/
def gbnd (m q u K₁ K₂ : ℕ) : ℕ :=
  if 0 < q ∧ 0 < u ∧ K₁ < K₂ ∧
      2 * SqueezeBench.Golomb.Lower.V003.blockLen K₂ ≤ SqueezeBench.Golomb.Lower.V002.bnd m q u then
    (2 * q * u * m + gain q K₁ K₂ - (u - 1) * u) / (q * (q + 1)) - u
  else 0

/-- The best pair of caps for a threshold `q` and a window length `u`, around
`K₁ ≈ q/3` and `K₂ ≈ 3q/5`. -/
def bestK (m q u : ℕ) : ℕ :=
  max (max (gbnd m q u (q / 3) (3 * q / 5)) (gbnd m q u (q / 3) (3 * q / 5 + 1)))
    (max (gbnd m q u (q / 3 + 1) (3 * q / 5)) (gbnd m q u (q / 3 + 1) (3 * q / 5 + 1)))

/-- The two window lengths around V002's maximiser. -/
def bestU (m q : ℕ) : ℕ :=
  max (bestK m q (SqueezeBench.Golomb.Lower.V002.uOf m q + 1))
    (bestK m q (SqueezeBench.Golomb.Lower.V002.uOf m q + 2))

/-- The best over the thresholds around `⌊√m⌋`. -/
def wRaw (m : ℕ) : ℕ :=
  max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m))
    (max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m + 1))
      (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m - 1)))

/-- The two-block boundary bound, pinned below `nMin`. -/
def w : BoundFn := pin nMin wRaw

/-- The record: V003 folded with the two-block boundary bound. -/
def record : BoundFn := maxWith SqueezeBench.Golomb.Lower.V003.record w

end SqueezeBench.Golomb.Lower.V004
