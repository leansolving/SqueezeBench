import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V002.Def

/-!
# Golomb lower-bound record V003 — the record function

V002 optimised the parameters of V001's master inequality

`2 * q * u * m ≤ (L + u) * q * (q + 1) + (u - 1) * u`,

which is tight for the linear program behind it. V003 adds the **boundary effect**, a new
constraint. The window ending at `s` holds marks in `[0, s]` only, and their pairwise
distances are distinct and lie in `[1, s]`, so it holds at most `K` marks as soon as
`2 * s < K * (K + 1)`; the same holds at the far end, where the window sees only
`[s - u + 1, L]`. On such a window the tangent estimate `2 * q * c ≤ c * (c - 1) + q(q+1)`
has slack `(q - c) * (q - c + 1) ≥ (q - K) * (q - K + 1)`. Taking the first and last
`K * (K + 1) / 2` windows gives

`2 * q * u * m + K * (K + 1) * (q - K) * (q - K + 1) ≤ (L + u) * q * (q + 1) + (u - 1) * u`.

With `K ≈ q / 2` the new term is about `q⁴ / 16 ≈ m² / 16`, worth about `m / 16` on the
bound, at every `m`.

The blocks must be disjoint, `2 * K * (K + 1) / 2 ≤ L`; this is guarded by comparing with
V002's `bnd`, which is already known to be at most `L`.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V003

open SqueezeBench

/-- The number of boundary windows used at each end, chosen so that a window there holds
at most `K` marks. -/
def blockLen (K : ℕ) : ℕ := K * (K + 1) / 2

/-- The total slack harvested from the two boundary blocks: `2 * blockLen K` windows, each
with slack at least `(q - K) * (q - K + 1)`. -/
def blockGain (q K : ℕ) : ℕ := K * (K + 1) * ((q - K) * (q - K + 1))

/-- The master inequality with the boundary gain, solved for `L`. The guard makes the
two blocks disjoint and keeps the degenerate parameters harmless. -/
def gbnd (m q u K : ℕ) : ℕ :=
  if 0 < q ∧ 0 < u ∧ 2 * blockLen K ≤ SqueezeBench.Golomb.Lower.V002.bnd m q u then
    (2 * q * u * m + blockGain q K - (u - 1) * u) / (q * (q + 1)) - u
  else 0

/-- The best window length for a threshold `q` and a cap `K`, around V002's maximiser. -/
def bestU (m q K : ℕ) : ℕ :=
  max (gbnd m q (SqueezeBench.Golomb.Lower.V002.uOf m q) K)
    (max (gbnd m q (SqueezeBench.Golomb.Lower.V002.uOf m q + 1) K)
      (gbnd m q (SqueezeBench.Golomb.Lower.V002.uOf m q + 2) K))

/-- The best cap for a threshold `q`, around `q / 2`. -/
def bestK (m q : ℕ) : ℕ :=
  max (bestU m q (q / 2)) (max (bestU m q (q / 2 + 1)) (bestU m q (q / 2 - 1)))

/-- The best over the thresholds around `⌊√m⌋`. -/
def wRaw (m : ℕ) : ℕ :=
  max (bestK m (SqueezeBench.Golomb.Lower.V001.qOf m))
    (max (bestK m (SqueezeBench.Golomb.Lower.V001.qOf m + 1))
      (bestK m (SqueezeBench.Golomb.Lower.V001.qOf m - 1)))

/-- The boundary bound, pinned below `nMin`. -/
def w : BoundFn := pin nMin wRaw

/-- The record: V002 folded with the boundary bound. -/
def record : BoundFn := maxWith SqueezeBench.Golomb.Lower.V002.record w

end SqueezeBench.Golomb.Lower.V003
