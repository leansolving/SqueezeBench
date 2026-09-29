import SqueezeBench.Problems.Ramsey.Records.Lower.V002.Def

/-! Record V003 for Ramsey, lower direction, by baseline claude-opus-5: the record function.
The bound is `max over k of 17^k · ⌊(n-1)/3^k⌋² + 1`: the `k`-fold lexicographic power of
the Paley graph on 17 vertices, with a block graph of size `⌊(n-1)/3^k⌋` at its innermost
level. -/

namespace SqueezeBench.Ramsey.Lower.V003

open SqueezeBench

-- The best candidate over the levels still fitting under `m`; structural in `fuel`, and
-- the powers are carried along, so the kernel evaluates it cheaply.
def go (m : ℕ) (fuel p3 p17 : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < p3 then 0 else max (p17 * (m / p3) ^ 2) (go m fuel (3 * p3) (17 * p17))

def w : BoundFn := pin nMin (fun n => go (n - 1) n 1 1 + 1)

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey.Lower.V002.record w

end SqueezeBench.Ramsey.Lower.V003
