import SqueezeBench.Problems.Roth.Records.Lower.V006.Def

/-! Record V007 for Roth, lower direction, by trial claude-fable: the record function.
The last-digit recursion of V002–V006 with the base window widened from `n ≤ 56` to
`n ≤ 209`, filled with the exact Roth numbers `r₃(n)` there (OEIS A003002). `Proof.lean`
certifies every entry by an explicit 3-AP-free set — one per jump node of `r₃` — taken from the
extremal sets published with A003002 (Wagstaff, Gasarch, Wróblewski, Cariboni). The recursion
above the window is multiplicative in its base, so the gain propagates to infinitely many `n`. -/

namespace SqueezeBench.Roth.Lower.V007

/-- `r₃(n)` for `n = 0, …, 209`, at index `n`. Every entry is a lower bound proved in
`Proof.lean` from an explicit set; the values are those of A003002. -/
def tblList : List ℕ :=
  [
    0, 1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6, 7, 8,
    8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 11, 11, 11, 11,
    12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 17, 17, 17, 18, 18, 18, 18, 19, 19,
    19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 22,
    22, 22, 22, 22, 22, 22, 22, 23, 23, 24, 24, 24, 24, 24, 24,
    24, 24, 25, 25, 25, 26, 26, 26, 26, 26, 27, 27, 27, 27, 28,
    28, 28, 28, 28, 28, 28, 29, 29, 29, 30, 30, 30, 30, 30, 30,
    30, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34,
    35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 37, 37,
    38, 38, 38, 38, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40,
    40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41,
    41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 43]

/-- The base table: the exact Roth number for `n ≤ 209`, and `0` beyond the table. -/
def tbl (n : ℕ) : ℕ := tblList.getD n 0

/-- The V002 last-digit recursion `f n ≥ f ⌈n/3⌉ + f ⌈(n-1)/3⌉`, bottoming out on the table
for `n ≤ 209`, and kept monotone as in V005 by carrying `tbl 209` upwards. Structural in the
fuel, so the kernel evaluates it. -/
def cntAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n ≤ 209 then tbl n
      else max (tbl 209) (cntAux fuel ((n + 2) / 3) + cntAux fuel ((n + 1) / 3))

def cnt : SqueezeBench.BoundFn := fun n => cntAux n n

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Roth.Lower.V006.record cnt

end SqueezeBench.Roth.Lower.V007
