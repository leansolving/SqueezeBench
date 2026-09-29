import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V007.Def

/-!
# Golomb lower-bound record V008 — the record function

A certificate checker for a family of Lindström-type inequalities. Sort the marks
`a₀ < … < a_{m-1}`, write `L' = a_{m-1} - a₀` and `b_r = (a_r - a₀) + (a_{m-1} - a_{m-1-r})`
for the total span of the first and last `r + 1` marks. For `u + 1 ≤ s` let `E(u, s)` be the
set of pairs of order `≤ u`, together with all pairs inside the first `s` or inside the last
`s` marks (`2 s ≤ m`, or `s = u + 1`, when it is the plain Lindström set). Its
`n(u, s) = M_u + (s - 1 - u)(s - u)` differences are distinct, and their sum is
`T_u L' - ∑_r neg(u, s, r) b_r + ∑_r pos(u, s, r) b_r` with
`neg = (u - r) + (s - 1 - u - r)`, `pos = r - u` for `r < s` (truncated subtraction). So

`n (n + 1) + 2 ∑_r neg · b_r ≤ u (u + 1) L' + 2 ∑_r pos · b_r`.

A certificate is a list of triples `(λ, u, s)`. If the weighted sums satisfy
`POS_r ≤ NEG_r` for every `r`, the `b_r` terms can be replaced by V007's lower bounds
`H _ 2 (r + 1) ≤ b_r` (two separated intervals), which gives a lower bound on `L'`.

The certificate is a chain `s_j = s₀ + j`, `u_j = 1 + ⌊j (s₀ + J - 3) / J⌋`,
`λ_j = (J + 1)² - j²` (`j ≤ J`), repaired top-down by plain Lindström sets wherever a net
coefficient is positive; six choices of `(s₀, J)` around `(3√m/4, 5√m/4 - 5)` are tried.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V008

open SqueezeBench

/-- The negative coefficient of `b_r` in the sum over `E(u, s)`. -/
def negC (u s r : ℕ) : ℕ := (u - r) + (s - 1 - u - r)

/-- The positive coefficient of `b_r` in the sum over `E(u, s)`. -/
def posC (u s r : ℕ) : ℕ := if r < s then r - u else 0

/-- The number of pairs in `E(u, s)`. -/
def nOf (m u s : ℕ) : ℕ := SqueezeBench.Golomb.Lower.V006.mOf m u + (s - 1 - u) * (s - u)

/-- Weighted negative coefficients of a certificate. -/
def negS (cs : List (ℕ × ℕ × ℕ)) (r : ℕ) : ℕ := (cs.map fun c => c.1 * negC c.2.1 c.2.2 r).sum

/-- Weighted positive coefficients of a certificate. -/
def posS (cs : List (ℕ × ℕ × ℕ)) (r : ℕ) : ℕ := (cs.map fun c => c.1 * posC c.2.1 c.2.2 r).sum

/-- Twice the weighted Lindström lower bounds. -/
def numS (m : ℕ) (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  (cs.map fun c => c.1 * (nOf m c.2.1 c.2.2 * (nOf m c.2.1 c.2.2 + 1))).sum

/-- Twice the weighted coefficient of the length. -/
def denS (cs : List (ℕ × ℕ × ℕ)) : ℕ := (cs.map fun c => c.1 * (c.2.1 * (c.2.1 + 1))).sum

/-- An admissible triple `(λ, u, s)`. -/
def okItem (m : ℕ) (c : ℕ × ℕ × ℕ) : Bool :=
  decide (1 ≤ c.2.1 ∧ c.2.1 + 1 ≤ c.2.2 ∧ c.2.2 ≤ m ∧ (c.2.2 = c.2.1 + 1 ∨ 2 * c.2.2 ≤ m))

/-- The certificate check. -/
def certOk (m R : ℕ) (cs : List (ℕ × ℕ × ℕ)) : Bool :=
  cs.all (okItem m) && cs.all (fun c => decide (c.2.2 ≤ R)) &&
    (List.range R).all (fun r => decide (posS cs r ≤ negS cs r)) && decide (0 < denS cs)

/-- V007's lower bound on `b_r`, where it applies. -/
def bLow (m r : ℕ) : ℕ :=
  if r = 0 ∨ m < 2 * r + 1 then 0 else SqueezeBench.Golomb.Lower.V007.H (r + 1) 2 (r + 1)

/-- The bound of a checked certificate, rounded up; `0` if the check fails. -/
def certBound (m R : ℕ) (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  if certOk m R cs = true then
    (numS m cs + 2 * ∑ r ∈ Finset.range R, (negS cs r - posS cs r) * bLow m r + (denS cs - 1))
      / denS cs
  else 0

/-- The chain of extended sets. -/
def chainItems (s₀ J : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (J + 1)).map fun j => ((J + 1) * (J + 1) - j * j, 1 + j * (s₀ + J - 3) / J, s₀ + j)

/-- Top-down repair: a plain Lindström set of order `r + 1` wherever `b_r` has a positive net
coefficient. -/
def repair (cs : List (ℕ × ℕ × ℕ)) : ℕ → List (ℕ × ℕ × ℕ)
  | 0 => cs
  | k + 1 =>
    repair (if posS cs (k + 1) ≤ negS cs (k + 1) then cs
      else (posS cs (k + 1) - negS cs (k + 1), k + 2, k + 3) :: cs) k

/-- One candidate certificate. -/
def cand (m s₀ J : ℕ) : ℕ :=
  if 2 ≤ s₀ ∧ 1 ≤ J then certBound m (s₀ + J + 3) (repair (chainItems s₀ J) (s₀ + J)) else 0

/-- The best of six candidates around `s₀ ≈ 3√m/4`, `J ≈ 5√m/4 - 5`. -/
def wRaw (m : ℕ) : ℕ :=
  max
    (max (cand m (3 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4)
            (5 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 - 6))
      (max (cand m (3 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4)
            (5 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 - 5))
        (cand m (3 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4)
            (5 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 - 4))))
    (max (cand m (3 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 + 1)
            (5 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 - 6))
      (max (cand m (3 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 + 1)
            (5 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 - 5))
        (cand m (3 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 + 1)
            (5 * SqueezeBench.Golomb.Lower.V001.isqrt m / 4 - 4))))

/-- The record: V007 folded with the certified bound. -/
def record : BoundFn := fun m => max (SqueezeBench.Golomb.Lower.V007.record m) (wRaw m)

end SqueezeBench.Golomb.Lower.V008
