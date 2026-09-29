import SqueezeBench.Problems.Ramsey.Records.Lower.V006.Def

/-! Record V007 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The bound is the alteration (deletion) form of Erdős' argument: for every `N`, some
2-colouring of `K_N` has at most `d = ⌊2·C(N,n) / 2^C(n,2)⌋` monochromatic `n`-sets, and
deleting one vertex from each leaves `N − d` vertices with none, so `f n ≥ N − d + 1`.
The record uses `d ≤ ⌊2·N^n / (n!·2^C(n,2))⌋` and picks `N` where the discrete derivative
of `N − 2·N^n/K` changes sign, i.e. the largest `N` with `2·n·N^(n−1) < K`, by a binary
search structural in its fuel. Validity holds for every `N`, so the choice is free. -/

namespace SqueezeBench.Ramsey.Lower.V007

-- Binary search for the largest `N` with `2 · n · N^(n−1) < K`; the returned value need
-- not be optimal, the bound below is valid at every `N`.
def bsearchD (n K : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if 2 * n * ((lo + hi) / 2) ^ (n - 1) < K then bsearchD n K fuel ((lo + hi) / 2) hi
    else bsearchD n K fuel lo ((lo + hi) / 2)

-- `N − ⌊2·N^n / K⌋`, the number of vertices surviving the deletion.
def altAt (n K N : ℕ) : ℕ := N - 2 * N ^ n / K

-- The alteration bound at the chosen `N`, with `K = n! · 2^(n(n−1)/2)` from V006.
def alt (n : ℕ) : ℕ :=
  altAt n (SqueezeBench.Ramsey.Lower.V006.thr n)
    (bsearchD n (SqueezeBench.Ramsey.Lower.V006.thr n) (n + 1) 0 (2 ^ n))

def v : SqueezeBench.BoundFn := SqueezeBench.pin SqueezeBench.Ramsey.nMin (fun n => alt n + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Ramsey.Lower.V006.record v

end SqueezeBench.Ramsey.Lower.V007
