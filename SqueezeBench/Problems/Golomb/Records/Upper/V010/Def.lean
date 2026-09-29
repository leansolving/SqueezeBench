import SqueezeBench.Problems.Golomb.Records.Upper.V009.Def

-- Golomb upper-bound record V010 — the record function.
-- Singer (1938): for a prime `q` and a generator `θ` of `GF(q³)ˣ`, the `q + 1` residues
-- `a < q² + q + 1` with `θᵃ ∈ GF(q) + GF(q)·θ` form a perfect difference set, in particular
-- a Sidon set modulo `q² + q + 1`. Rotated into a window as in V008 (`q + 1` residues modulo
-- `q² + q + 1`, so a window of length `(m-1)·q` holds `m` of them when `m ≤ q + 1`), this gives
-- `f m ≤ (m-1)·q` for every prime `q ≥ m - 1`. Here `q = primeGe (m-1)` (V009) is the least
-- prime `≥ m - 1`, so when `m - 1` is prime the bound is `(m-1)²`, which beats V009's
-- `⌊(m-1)(p²-1)/p⌋` with `p ≥ m + 1` by more than `m - 1`.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Golomb.Upper.V010

open SqueezeBench

/-- Singer's bound `(m-1)·q`, with `q` the least prime `≥ m - 1`. -/
def singerLen (m : ℕ) : ℕ := (m - 1) * SqueezeBench.Golomb.Upper.V009.primeGe (m - 1)

/-- The previous record folded with Singer's bound. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V009.record singerLen

end SqueezeBench.Golomb.Upper.V010
