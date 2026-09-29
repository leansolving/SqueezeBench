import SqueezeBench.Problems.Golomb.Records.Upper.V010.Def

-- Golomb upper-bound record V011 — the record function.
-- Singer's construction (V010) works over any finite field `GF(q)`, `q = p^k` a prime power:
-- `q + 1` residues Sidon modulo `q² + q + 1`, hence `f m ≤ (m-1)·q` for `m ≤ q + 1`. V010 used
-- primes only; here `q = primePowGe (m-1)` is the least *prime power* `≥ m - 1`, so the bound
-- improves exactly when the least prime power `≥ m - 1` is not a prime — `m = 33` (`q = 32`),
-- `m = 49, 50` (`q = 49`), `m = 63, 64, 65` (`q = 64`), and so on for every prime power.
-- Mathlib's decidability of `IsPrimePow` makes the search plain kernel arithmetic.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Golomb.Upper.V011

open SqueezeBench

/-- The least prime power `≥ m`, found among `m, …, 2m`. -/
def primePowGe (m : ℕ) : ℕ :=
  match (List.range (m + 1)).find? (fun d => decide (IsPrimePow (m + d))) with
  | some d => m + d
  | none => 0

/-- Singer's bound `(m-1)·q`, with `q` the least prime power `≥ m - 1`. -/
def singerPPLen (m : ℕ) : ℕ := (m - 1) * primePowGe (m - 1)

/-- The previous record folded with the prime-power Singer bound. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V010.record singerPPLen

end SqueezeBench.Golomb.Upper.V011
