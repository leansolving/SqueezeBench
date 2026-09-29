import SqueezeBench.Problems.Ramsey.Records.Lower.V005.Def

/-! Record V006 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The bound is Erdős' counting bound in its sharp form: `f n ≥ M + 1` for the largest `M`
with `2 · M^n < n! · 2^(n(n-1)/2)`, since then `2 · C(M, n) < 2^C(n,2)` and a
2-colouring of `K_M` without a monochromatic `K_n` exists by counting. `M` is found by a
binary search on the monotone predicate, structural in its fuel; every candidate is a
single kernel-accelerated power, so the kernel evaluates the record in `O(n)` steps. -/

namespace SqueezeBench.Ramsey.Lower.V006

-- `n!`, structural in `n` so that the kernel unfolds it directly.
def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

-- The threshold `n! · 2^(n(n-1)/2)`.
def thr (n : ℕ) : ℕ := fact n * 2 ^ (n * (n - 1) / 2)

-- Binary search for the largest `M` with `2 · M^n < K`; `lo` always satisfies the
-- predicate and is what is returned, so the result is sound whatever the fuel.
def bsearch (n K : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if 2 * ((lo + hi) / 2) ^ n < K then bsearch n K fuel ((lo + hi) / 2) hi
    else bsearch n K fuel lo ((lo + hi) / 2)

-- The largest `M < 2^n` with `2 · M^n < n! · 2^(n(n-1)/2)`.
def erdos (n : ℕ) : ℕ := bsearch n (thr n) (n + 1) 0 (2 ^ n)

def v : SqueezeBench.BoundFn := SqueezeBench.pin SqueezeBench.Ramsey.nMin (fun n => erdos n + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Ramsey.Lower.V005.record v

end SqueezeBench.Ramsey.Lower.V006
