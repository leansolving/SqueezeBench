import SqueezeBench.Problems.Ramsey.Records.Lower.V004.Def

/-! Record V005 for Ramsey, lower direction, by baseline claude-opus-5: the record function.
The bound is `max over k of 37^k · ⌊(n-1)/4^k⌋² + 1`: the `k`-fold lexicographic power of
the Paley graph on 37 vertices, with a block graph of size `⌊(n-1)/4^k⌋` at its innermost
level. -/

namespace SqueezeBench.Ramsey.Lower.V005

open SqueezeBench

-- The best candidate over the levels still fitting under `m`; structural in `fuel`, and
-- the powers are carried along, so the kernel evaluates it cheaply.
def go (m : ℕ) (fuel p4 p37 : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < p4 then 0 else max (p37 * (m / p4) ^ 2) (go m fuel (4 * p4) (37 * p37))

def w : BoundFn := pin nMin (fun n => go (n - 1) n 1 1 + 1)

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey.Lower.V004.record w

end SqueezeBench.Ramsey.Lower.V005
