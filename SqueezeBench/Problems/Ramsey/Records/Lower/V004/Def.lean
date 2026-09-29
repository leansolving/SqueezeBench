import SqueezeBench.Problems.Ramsey.Records.Lower.V003.Def

/-! Record V004 for Ramsey, lower direction, by baseline claude-opus-5: the record function.
The bound is `max over a, b of 5^a · 17^b · ⌊(n-1)/(2^a·3^b)⌋² + 1`: `a` levels of the
5-cycle over `b` levels of the Paley graph on 17 vertices over a block graph. -/

namespace SqueezeBench.Ramsey.Lower.V004

open SqueezeBench

-- The levels of the Paley graph, for a fixed number of 5-cycle levels; `d` is the clique
-- factor `2^a·3^b` and `p` the vertex factor `5^a·17^b`.
def goB (m : ℕ) (fuel d p : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < d then 0 else max (p * (m / d) ^ 2) (goB m fuel (3 * d) (17 * p))

-- The levels of the 5-cycle, each opening a fresh fold over the Paley levels.
def goA (m : ℕ) (fuel d p : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < d then 0 else max (goB m (fuel + 1) d p) (goA m fuel (2 * d) (5 * p))

def w : BoundFn := pin nMin (fun n => goA (n - 1) n 1 1 + 1)

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey.Lower.V003.record w

end SqueezeBench.Ramsey.Lower.V004
