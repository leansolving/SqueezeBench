import SqueezeBench.Problems.Golomb.Records.Upper.V008.Def

-- Golomb upper-bound record V009 — the record function.
-- Bose–Chowla (1962): for a prime `p` and a generator `θ` of `GF(p²)ˣ`, the `p` discrete
-- logarithms `a` with `θᵃ ∈ θ + GF(p)` form a Sidon set modulo `p² - 1`. Rotated into a window
-- as in V008 (`p` residues modulo `p² - 1`, so a window of length `⌊(m-1)(p²-1)/p⌋` holds `m`
-- of them), this gives `f m ≤ ⌊(m-1)(p²-1)/p⌋` for every prime `p ≥ m`. Here `p = primeGe m`
-- is the least prime `≥ m` — `m` itself when `m` is prime, which is where this beats V008's
-- `(m-1)·nextPrime m` by about `3m`; elsewhere it beats it by one.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Golomb.Upper.V009

open SqueezeBench

/-- The least prime `≥ m`, found among `m, …, 2m`. -/
def primeGe (m : ℕ) : ℕ :=
  match (List.range (m + 1)).find? (fun d => decide (Nat.Prime (m + d))) with
  | some d => m + d
  | none => 0

/-- Bose–Chowla's bound `⌊(m-1)(p²-1)/p⌋`, with `p` the least prime `≥ m`. -/
def bcLen (m : ℕ) : ℕ := (m - 1) * (primeGe m ^ 2 - 1) / primeGe m

/-- The previous record folded with the Bose–Chowla bound. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V008.record bcLen

end SqueezeBench.Golomb.Upper.V009
