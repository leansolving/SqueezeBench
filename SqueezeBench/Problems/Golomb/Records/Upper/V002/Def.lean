import SqueezeBench.Problems.Golomb.Records.Upper.V001.Def

/-!
# Golomb upper-bound record V002 — the record function

The same Erdős–Turán ruler as V001, but measured at the *least* prime above `m` instead of
at Bertrand's worst case `2m`. The length is then `2p(m-1) + ((m-1)² mod p)` with `p` the
least prime `> m`, which is about `2m²` rather than `4m²`.

`nextPrime` searches the offsets `0, …, m` and so always succeeds for `m ≥ 1`, by Bertrand's
postulate; the `none` branch is unreachable there. Both the search and the length are plain
`Nat` arithmetic, so the kernel evaluates them cheaply.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Upper.V002

open SqueezeBench

/-- The least prime `> m`, found among `m+1, …, 2m+1`. -/
def nextPrime (m : ℕ) : ℕ :=
  match (List.range (m + 1)).find? (fun d => decide (Nat.Prime (m + 1 + d))) with
  | some d => m + 1 + d
  | none => 0

/-- The length of the `m`-mark Erdős–Turán ruler modulo `nextPrime m`. -/
def etLen (m : ℕ) : ℕ := 2 * nextPrime m * (m - 1) + (m - 1) ^ 2 % nextPrime m

/-- The previous record folded with the sharpened Erdős–Turán bound. -/
def record : SqueezeBench.BoundFn := minWith SqueezeBench.Golomb.Upper.V001.record etLen

end SqueezeBench.Golomb.Upper.V002
