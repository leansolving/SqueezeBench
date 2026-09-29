import SqueezeBench.Problems.Ramsey.Records.Upper.V001.Def

/-! Record V002 for Ramsey, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The Erdős–Szekeres table of V001 (with the parity saving) is sharpened at every interior entry
by the counting bound of Walker (1968), in the off-diagonal form of Li–Rousseau–Zang (2004):
if `A = R(s, t+2)` and `C = R(s+2, t)` then `R(s+2, t+2) ≤ x + 1` whenever
`3x² > 6x(A+C) + (A-C)²`. Counting paths of length two, adjacent pairs have fewer than `A`
common neighbours and non-adjacent pairs fewer than `C` common non-neighbours, which with
Cauchy–Schwarz is impossible on `x + 1` vertices. `crit` is that criterion in ℕ, without
subtraction. The least such `x` is `A + C + 1 + ⌊√(4(A² + AC + C²)/3)⌋`; `isqrtAux` is
Newton's iteration for the square root, and `walker` re-checks `crit` at the value it returns,
so the proofs depend only on the check, never on the search.

The table is stored by antidiagonals as in V001: `rows k` is the pair of antidiagonals `k + 1`
and `k`, and `next` computes antidiagonal `k + 2` from them; entry `j` of antidiagonal `k`
bounds `R(j, k + 2 - j)`. Since `R(s,t) = R(t,s)`, entries past the middle of an antidiagonal
are read mirrored (`mir`), which halves the work of the kernel. -/

namespace SqueezeBench.Ramsey.Upper.V002

open SqueezeBench

-- The counting criterion at `x`: `3x² > 6x(A+C) + (A-C)²`.
def crit (A C x : ℕ) : Bool := 6 * x * (A + C) + A * A + C * C < 3 * x * x + 2 * A * C

-- Newton's iteration for `⌊√N⌋`, started above the root; stops as soon as it stops decreasing.
def isqrtAux (N : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | fuel + 1, g => let g' := (g + N / g) / 2; if g' < g then isqrtAux N fuel g' else g

-- The counting bound, capped by the Erdős–Szekeres value `es`; the value returned is certified.
def walker (A C es : ℕ) : ℕ :=
  let P := A + C
  if es ≤ 2 * P + 1 then es
  else
    let x := P + 1 + isqrtAux (4 * (A * A + A * C + C * C) / 3) 12
      (P + (A * A + C * C - 2 * A * C) / (6 * P) + 1)
    if crit A C x then min es (x + 1)
    else if crit A C (x + 1) then min es (x + 1 + 1)
    else es

-- Entry `j` of an antidiagonal whose two indices sum to `m`, read mirrored when `2j > m`.
def mir (f : ℕ → ℕ) (m j : ℕ) : ℕ := if m < 2 * j then f (m - j) else f j

-- Antidiagonal `k + 2` from antidiagonals `k + 1` (`p1`) and `k` (`p2`).
def next (k : ℕ) (p1 p2 : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 =>
    if i ≤ k then
      walker (mir p2 (k + 2) i) (mir p2 (k + 2) (i + 2))
        (SqueezeBench.Ramsey.Upper.V001.stepVal (mir p1 (k + 3) (i + 1)) (mir p1 (k + 3) (i + 2)))
    else if i = k + 1 then 1
    else 0

-- Antidiagonals `0` and `1`, as in V001.
def row0 : ℕ → ℕ := fun i => if i = 1 then 1 else 0

def row1 : ℕ → ℕ := fun i =>
  if i = 0 then 0 else SqueezeBench.Ramsey.Upper.V001.stepVal (row0 (i - 1)) (row0 i)

-- `rows k = (antidiagonal (k + 1), antidiagonal k)`.
def rows : ℕ → (ℕ → ℕ) × (ℕ → ℕ)
  | 0 => (row1, row0)
  | k + 1 => (next k (rows k).1 (rows k).2, (rows k).1)

def record : SqueezeBench.BoundFn := fun n => (rows (2 * n - 3)).1 n

end SqueezeBench.Ramsey.Upper.V002
