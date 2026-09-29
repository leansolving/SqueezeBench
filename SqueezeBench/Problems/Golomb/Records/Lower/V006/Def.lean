import SqueezeBench.Problems.Golomb.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V005.Def

/-!
# Golomb lower-bound record V006 — the record function

Lindström's argument with a boundary correction. Sort the marks `a₀ < … < a_{m-1}` of a ruler
of length `L`. The `M = ∑_{j=1}^{t} (m - j)` differences `a_{i+j} - a_i` of order `j ≤ t` are
distinct positive integers, so their sum is at least `M (M + 1) / 2`. The sum of the order-`j`
differences telescopes to `∑_{r<j} (a_{m-j+r} - a_r)`, and the first `r + 1` marks span at
least `f (r + 1)`, as do the last `r + 1`. With any valid lower bound `g` and
`G j = g 1 + … + g j`,

`M (M + 1) + 4 ∑_{j=1}^{t} G j ≤ t (t + 1) L`.

The bound is bootstrapped: `g` is the record itself at the smaller arguments `≤ t ≈ √m`,
computed with structural fuel. Only the orders `t = ⌊√m⌋ - 1, ⌊√m⌋` are tried; over
`1 ≤ m ≤ 1000` no other order does better.

Definitions only; validity is proved in `Proof.lean`.
-/

namespace SqueezeBench.Golomb.Lower.V006

open SqueezeBench

/-- The prefix sums `G j = g 1 + … + g j`. -/
def gsum (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => gsum g j + g (j + 1)

/-- `G 1 + … + G t`, the boundary correction at order `t`. -/
def ggsum (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => ggsum g t + gsum g (t + 1)

/-- The number of differences of order at most `t` among `m` marks. -/
def mOf (m t : ℕ) : ℕ := t * m - t * (t + 1) / 2

/-- Lindström's bound at order `t`, with the boundary correction from `g`, rounded up. -/
def lind (g : ℕ → ℕ) (m t : ℕ) : ℕ :=
  if 0 < t ∧ t < m then
    (mOf m t * (mOf m t + 1) + 4 * ggsum g t + (t * (t + 1) - 1)) / (t * (t + 1))
  else 0

/-- The bootstrapped bound: V005's record, or Lindström's bound fed with the level below. -/
def core : ℕ → ℕ → ℕ
  | 0, m => SqueezeBench.Golomb.Lower.V005.record m
  | k + 1, m =>
    max (SqueezeBench.Golomb.Lower.V005.record m)
      (max (lind (core k) m (SqueezeBench.Golomb.Lower.V001.isqrt m - 1))
        (lind (core k) m (SqueezeBench.Golomb.Lower.V001.isqrt m)))

/-- The record: the bootstrapped bound with fuel `m`. -/
def record : BoundFn := fun m => core m m

end SqueezeBench.Golomb.Lower.V006
