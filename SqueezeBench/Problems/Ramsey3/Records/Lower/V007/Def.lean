import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V006.Def

-- Record V007 for Ramsey3, lower direction, by trial claude-fable.
--
-- The exponent `3/2`: for a prime `q`, the ordered point–line incidence graph of the affine
-- plane over `Z/q` (flags `(point, non-vertical line)`, two flags adjacent when their lines
-- differ and the smaller point lies on the other's line) is triangle-free on `q³` vertices with
-- independence number at most `2q²`. So `R(3,k) > q³` for the largest prime `q` with
-- `2q² ≤ k - 1`, i.e. `R(3,k) = Ω(k^{3/2})`; this beats the `k^{1.29}` recursion of V005/V006
-- from `k = 1683` on (in stretches) and at every `k ≥ 8979`. Folded into V006's record.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V007

open SqueezeBench

-- Primality by trial division.
def isPrime (n : ℕ) : Bool := 2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

-- The integer square root by linear search: the largest `s` with `s * s ≤ n`.
def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, s, _ => s
  | f + 1, s, n => if (s + 1) * (s + 1) ≤ n then isqrtAux f (s + 1) n else s

def isqrt (n : ℕ) : ℕ := isqrtAux n 0 n

-- The largest prime `≤ t`, or `0`.
def primeBelowAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, t => if isPrime t then t else primeBelowAux f (t - 1)

def primeBelow (t : ℕ) : ℕ := primeBelowAux t t

-- `q³` for the largest prime `q` with `2 q² ≤ m` (`0` if there is none).
def inc (m : ℕ) : ℕ :=
  primeBelow (isqrt (m / 2)) * (primeBelow (isqrt (m / 2)) * primeBelow (isqrt (m / 2)))

-- The new bound, padded with `0` below `nMin`.
def v : SqueezeBench.BoundFn := pin nMin (fun k => inc (k - 1) + 1)

-- Folded into the previous record, which is larger at every `k < 1683`.
def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey3.Lower.V006.record v

end SqueezeBench.Ramsey3.Lower.V007
