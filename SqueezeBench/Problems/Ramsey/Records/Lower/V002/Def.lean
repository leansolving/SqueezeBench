import SqueezeBench.Problems.Ramsey.Records.Lower.V001.Def

/-! Record V002 for Ramsey, lower direction, by baseline claude-opus-5: the record function.
The bound is `max over k of 5^k · ⌊(n-1)/2^k⌋² + 1`: the `k`-fold lexicographic power of
the 5-cycle, with a block graph of size `⌊(n-1)/2^k⌋` at its innermost level. -/

namespace SqueezeBench.Ramsey.Lower.V002

open SqueezeBench

def cand (n k : ℕ) : ℕ := 5 ^ k * ((n - 1) / 2 ^ k) ^ 2

-- The best candidate over all levels up to `k`; structural in `k`, so the kernel
-- evaluates it cheaply.
def bestUpTo (n : ℕ) (k : ℕ) : ℕ :=
  match k with
  | 0 => cand n 0
  | k + 1 => max (bestUpTo n k) (cand n (k + 1))

def w : BoundFn := pin nMin (fun n => bestUpTo n n + 1)

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey.Lower.V001.record w

end SqueezeBench.Ramsey.Lower.V002
