import SqueezeBench.Problems.Ramsey.Records.Lower.V009.Def

/-! Record V010 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V010.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The bound is Spencer's, from the symmetric Lovász Local Lemma in its `4pd ≤ 1` form:
`f n ≥ N + 1` whenever `8 · C(n,2) · C(N−2, n−2) ≤ 2^C(n,2)`. The record uses the
search-friendly sufficient condition `8 · C(n,2) · (N−2)^(n−2) ≤ (n−2)! · 2^C(n,2)`
(as `(n−2)! · C(N−2, n−2) ≤ (N−2)^(n−2)`) and takes the largest such `N` below `2^n` by a
binary search structural in its fuel, one kernel-accelerated power per step, as V006 does. -/

namespace SqueezeBench.Ramsey.Lower.V010

-- Binary search for the largest `N` with `8 · C(n,2) · (N−2)^(n−2) ≤ K`; `lo` always
-- satisfies the predicate and is what is returned.
def bsearch (n K : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if 8 * (n * (n - 1) / 2) * ((lo + hi) / 2 - 2) ^ (n - 2) ≤ K then
      bsearch n K fuel ((lo + hi) / 2) hi
    else bsearch n K fuel lo ((lo + hi) / 2)

-- The largest `N < 2^n` with `8 · C(n,2) · (N−2)^(n−2) ≤ (n−2)! · 2^(n(n−1)/2)`.
def lll (n : ℕ) : ℕ :=
  bsearch n (SqueezeBench.Ramsey.Lower.V006.fact (n - 2) * 2 ^ (n * (n - 1) / 2)) (n + 1) 0 (2 ^ n)

-- Pinned below `3`: the local lemma needs `2^C(n,2) > 4`.
def v : SqueezeBench.BoundFn := SqueezeBench.pin 3 (fun n => lll n + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Ramsey.Lower.V009.record v

end SqueezeBench.Ramsey.Lower.V010
