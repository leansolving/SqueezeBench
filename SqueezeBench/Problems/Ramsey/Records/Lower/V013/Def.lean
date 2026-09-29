import SqueezeBench.Problems.Ramsey.Records.Lower.V012.Def

/-! Record V013 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V013.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

Exact binomial coefficients in the two probabilistic bounds. V012's Spencer search used
`C(N−2, n−2) ≤ (N−2)^(n−2)/(n−2)!`; here its result is pushed upward while the exact
condition `2·(C(n,2)·C(N−2,n−2) + 1)·2718281829 ≤ 2^C(n,2)·10^9` still holds. V007's
alteration bound used `C(N,n) ≤ N^n/n!`; here `N − ⌊2·C(N,n)/2^C(n,2)⌋` is maximised
exactly over a window above V007's choice of `N`. Binomials are computed by the
multiplicative recurrence, structural in the lower index. -/

namespace SqueezeBench.Ramsey.Lower.V013

-- `C(N, k)` by the recurrence `C(N, k+1) = C(N, k) · (N − k) / (k + 1)`.
def binom (N : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => binom N k * (N - k) / (k + 1)

-- Spencer's exact condition at `N`.
def okS (n N : ℕ) : Bool :=
  2 * (n * (n - 1) / 2 * binom (N - 2) (n - 2) + 1) * 2718281829 ≤ 2 ^ (n * (n - 1) / 2) * 10 ^ 9

-- Push `N` upward while the condition holds; the result satisfies it whenever the start does.
def scanS (n : ℕ) : ℕ → ℕ → ℕ
  | 0, N => N
  | fuel + 1, N => if okS n (N + 1) then scanS n fuel (N + 1) else N

def spencerE (n : ℕ) : ℕ := scanS n 200 (SqueezeBench.Ramsey.Lower.V012.spencer n)

-- The exact alteration bound at `N`: the survivors after deleting one vertex per
-- monochromatic `n`-set.
def gA (n N : ℕ) : ℕ := N - 2 * binom N n / 2 ^ (n * (n - 1) / 2)

-- Its maximum over a window of `fuel` values from `N`.
def scanA (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, best => best
  | fuel + 1, N, best => scanA n fuel (N + 1) (max best (gA n N))

def altE (n : ℕ) : ℕ :=
  scanA n 40 (SqueezeBench.Ramsey.Lower.V007.bsearchD n (SqueezeBench.Ramsey.Lower.V006.thr n)
    (n + 1) 0 (2 ^ n)) 0

def v : SqueezeBench.BoundFn := SqueezeBench.pin 3 (fun n => max (spencerE n) (altE n) + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Ramsey.Lower.V012.record v

end SqueezeBench.Ramsey.Lower.V013
