import SqueezeBench.Problems.Golomb.Records.Upper.V005.Def

-- Golomb upper-bound record V006 — the record function.
-- Ruzsa's construction (1993): for a prime `p` and a primitive root `g` modulo `p`, the `p - 1`
-- residues `x ≡ i (mod p-1)`, `x ≡ -gⁱ (mod p)`, `i < p - 1`, form a Sidon set modulo `p(p-1)`.
-- Their representatives in `[0, p(p-1))` are therefore a Golomb ruler with `p - 1` marks and
-- length at most `p(p-1) - 1`. With `p = nextPrime m` (V002, the least prime above `m`) this
-- gives `f m ≤ p(p-1) - 1 ≈ m²`, against the `≈ 2m²` of the Erdős–Turán ruler used so far.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Golomb.Upper.V006

open SqueezeBench

/-- Ruzsa's bound `p(p-1) - 1`, with `p` the least prime above `m`. -/
def ruzsaLen (m : ℕ) : ℕ :=
  SqueezeBench.Golomb.Upper.V002.nextPrime m
    * (SqueezeBench.Golomb.Upper.V002.nextPrime m - 1) - 1

/-- The previous record folded with Ruzsa's bound. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V005.record ruzsaLen

end SqueezeBench.Golomb.Upper.V006
