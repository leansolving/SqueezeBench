import SqueezeBench.Problems.Ramsey.Records.Lower.V011.Def

/-! Record V012 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V012.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

Spencer's bound in its exact form: the symmetric Lovász Local Lemma with the condition
`e · p · (d + 1) ≤ 1`, `p = 2^(1−C(n,2))`, `d = C(n,2) · C(N−2, n−2)`, gives `f n ≥ N + 1`.
The record uses `C(N−2, n−2) ≤ (N−2)^(n−2)/(n−2)!` and the rational upper bound
`e < 2718281829 / 10^9`, so the searched predicate is
`2 · (C(n,2) · (N−2)^(n−2) + (n−2)!) · 2718281829 ≤ 2^C(n,2) · (n−2)! · 10^9`, and takes
the largest such `N` below `2^n` by a binary search structural in its fuel. -/

namespace SqueezeBench.Ramsey.Lower.V012

-- Binary search for the largest `N` with `2 · (C(n,2) · (N−2)^(n−2) + (n−2)!) · 2718281829 ≤ K`;
-- `lo` always satisfies the predicate and is what is returned.
def bsearch (n F K : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if 2 * (n * (n - 1) / 2 * ((lo + hi) / 2 - 2) ^ (n - 2) + F) * 2718281829 ≤ K then
      bsearch n F K fuel ((lo + hi) / 2) hi
    else bsearch n F K fuel lo ((lo + hi) / 2)

-- The largest `N < 2^n` satisfying the predicate with `F = (n−2)!` and
-- `K = 2^(n(n−1)/2) · (n−2)! · 10^9`.
def spencer (n : ℕ) : ℕ :=
  bsearch n (SqueezeBench.Ramsey.Lower.V006.fact (n - 2))
    (2 ^ (n * (n - 1) / 2) * SqueezeBench.Ramsey.Lower.V006.fact (n - 2) * 10 ^ 9)
    (n + 1) 0 (2 ^ n)

-- Pinned below `3`, where the condition cannot hold.
def v : SqueezeBench.BoundFn := SqueezeBench.pin 3 (fun n => spencer n + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Ramsey.Lower.V011.record v

end SqueezeBench.Ramsey.Lower.V012
