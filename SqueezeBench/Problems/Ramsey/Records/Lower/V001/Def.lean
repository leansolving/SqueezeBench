import SqueezeBench.Problems.Ramsey.Records.Lower.V000.Def

/-! Record V001 for Ramsey, lower direction, by baseline claude-opus-5: the record function.
The bound is `5 ^ ⌊log₂ (n-1)⌋ + 1`, from the lexicographic powers of the 5-cycle, folded
into the previous record by `maxWith`. -/

namespace SqueezeBench.Ramsey.Lower.V001

open SqueezeBench

-- `blog fuel m = ⌊log₂ m⌋` once `fuel` is large enough; structural in `fuel`, so the
-- kernel evaluates it cheaply.
def blog (fuel m : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < 2 then 0 else blog fuel (m / 2) + 1

def v : BoundFn := pin nMin (fun n => 5 ^ blog n (n - 1) + 1)

def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey.Lower.V000.record v

end SqueezeBench.Ramsey.Lower.V001
