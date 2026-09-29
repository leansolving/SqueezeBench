import SqueezeBench.Problems.Golomb.Records.Upper.V007.Def

-- Golomb upper-bound record V008 — the record function.
-- Ruzsa's ruler (V006) is a Sidon set *modulo* `p(p-1)` with `p - 1` residues, so it can be
-- rotated: some cyclic window of length `(m-1)·p` contains at least `m` of its residues, by
-- double counting (`p - 1` residues, each in `(m-1)p + 1` windows, against `p(p-1)` windows
-- holding at most `m - 1` each). Those `m` residues are an `m`-mark ruler of length at most
-- `(m-1)·p`, with `p = nextPrime m` (V002, the least prime above `m`): `f m ≤ (m-1) p` in place
-- of V006's `p(p-1) - 1`. Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Golomb.Upper.V008

open SqueezeBench

/-- The rotated Ruzsa bound `(m-1)·p`, with `p` the least prime above `m`. -/
def winLen (m : ℕ) : ℕ := (m - 1) * SqueezeBench.Golomb.Upper.V002.nextPrime m

/-- The previous record folded with the rotated Ruzsa bound. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V007.record winLen

end SqueezeBench.Golomb.Upper.V008
