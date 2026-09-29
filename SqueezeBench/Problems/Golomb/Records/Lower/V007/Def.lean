import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V006.Def

/-!
# Golomb lower-bound record V007 — the record function

V006's Lindström bound with the boundary terms bounded **jointly**. Call a family of `k`
index intervals of `n` consecutive marks each *separated* if any two share at most one mark;
then no pair of marks lies in two of them, so all their differences are distinct.
`H fuel k n` bounds the total span of such a family from below: the `k (u n − u(u+1)/2)`
differences of order `≤ u` inside the intervals are distinct, so (Lindström)

`Q (Q + 1) + 2 ∑_{o ≤ u} ∑_{1 ≤ r < o} b_r ≤ u (u + 1) · (total span)`,

where `b_r` is the total span of the `2k` end pieces of `r + 1` marks, again a separated
family when `2 r ≤ n − 1`, bounded by `H` with `2k` intervals. The record is `H` for one
interval, the whole ruler. For two end pieces this is the observation that the first and
last `r + 1` marks share no pair; it roughly doubles V006's boundary correction.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V007

open SqueezeBench

/-- `∑_{j < u} gsum g j`, the double boundary sum. -/
def bsum (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | u + 1 => bsum g u + SqueezeBench.Golomb.Lower.V006.gsum g u

/-- Lindström's bound at order `u` for a separated family of `k` intervals of `n` marks,
with `h (r + 1)` bounding the end pieces of `r + 1` marks; rounded up. -/
def lindK (h : ℕ → ℕ) (k n u : ℕ) : ℕ :=
  if 0 < u ∧ u < n ∧ 2 * u ≤ n + 1 then
    (k * SqueezeBench.Golomb.Lower.V006.mOf n u * (k * SqueezeBench.Golomb.Lower.V006.mOf n u + 1)
        + 2 * bsum (fun i => h (i + 1)) u + (u * (u + 1) - 1)) / (u * (u + 1))
  else 0

/-- The joint bound on `k` separated intervals of `n` marks, with structural fuel. -/
def H : ℕ → ℕ → ℕ → ℕ
  | 0, k, n => k * SqueezeBench.Golomb.Lower.V006.record n
  | f + 1, k, n =>
    max (k * SqueezeBench.Golomb.Lower.V006.record n)
      (max
        (max (lindK (H f (2 * k)) k n (SqueezeBench.Golomb.Lower.V001.isqrt n - 2))
          (lindK (H f (2 * k)) k n (SqueezeBench.Golomb.Lower.V001.isqrt n - 1)))
        (max (lindK (H f (2 * k)) k n (SqueezeBench.Golomb.Lower.V001.isqrt n))
          (lindK (H f (2 * k)) k n (SqueezeBench.Golomb.Lower.V001.isqrt n + 1))))

/-- The record: the joint bound for the whole ruler, one interval of `m` marks. -/
def record : BoundFn := fun m => H m 1 m

end SqueezeBench.Golomb.Lower.V007
