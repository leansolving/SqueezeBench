import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V001.Def

/-!
# Golomb lower-bound record V002 — the record function

V001 solved the master inequality

`2 * q * u * m ≤ (L + u) * q * (q + 1) + (u - 1) * u`

at one pair `(q, u)`, namely `q = ⌊√m⌋` and `u = q m − q(q+1)/2 + 1`. The inequality holds
for **every** pair, so the best bound is the maximum over pairs. For a fixed `q` the
right-hand side is a downward parabola in `u` whose real maximiser is
`q m − (q² + q − 1)/2`, so the integer optimum is one of three consecutive values; and the
best `q` is one of the four integers around `⌊√m⌋`. Taking the maximum over those twelve
pairs reaches the exact integer optimum of the master inequality at every `m` tested.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V002

open SqueezeBench

/-- The master inequality solved for `L`, at threshold `q` and window length `u`. -/
def bnd (m q u : ℕ) : ℕ := (2 * q * u * m - (u - 1) * u) / (q * (q + 1)) - u

/-- The real maximiser of `bnd m q ·`, rounded down. -/
def uOf (m q : ℕ) : ℕ := q * m - q * (q + 1) / 2

/-- The best window length for a given threshold. -/
def bestU (m q : ℕ) : ℕ :=
  max (bnd m q (uOf m q)) (max (bnd m q (uOf m q + 1)) (bnd m q (uOf m q + 2)))

/-- The best over the thresholds around `⌊√m⌋`. -/
def wRaw (m : ℕ) : ℕ :=
  max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m - 1))
    (max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m))
      (max (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m + 1))
        (bestU m (SqueezeBench.Golomb.Lower.V001.qOf m + 2))))

/-- The window bound, pinned below `nMin`. -/
def w : BoundFn := pin nMin wRaw

/-- The record: V001 folded with the optimised window bound. -/
def record : BoundFn := maxWith SqueezeBench.Golomb.Lower.V001.record w

end SqueezeBench.Golomb.Lower.V002
