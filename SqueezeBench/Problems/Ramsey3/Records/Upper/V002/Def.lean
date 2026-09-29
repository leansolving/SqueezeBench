import SqueezeBench.Problems.Ramsey3.Records.Upper.V001.Def

/-! Record V002 for Ramsey3, upper direction, by trial claude-fable: the record function.

Shearer's degree-sequence bound (J. B. Shearer, *On the independence number of sparse graphs*,
Random Structures Algorithms 7 (1995), 269–271): a triangle-free graph with degrees `d₁, …, dₙ`
has an independent set of size at least `Σᵢ f(dᵢ)`, where `f 0 = 1` and
`f d = (1 + (d² - d) f (d-1)) / (d² + 1)`. In a graph with no independent `k`-set every degree
is at most `k - 1`, and `f` is decreasing, so `n · f(k-1) ≤ k - 1` and hence
`R(3,k) ≤ ⌊(k-1) / f(k-1)⌋ + 1`, which is `(1 + o(1)) k² / log k`.

`f d` is the rational `(shearer d).1 / (shearer d).2`; both coordinates stay in ℕ so that the
record evaluates by kernel arithmetic alone. `minWith` keeps the previous record where the new
bound is not better (`k ≤ 6`, and `k = 0` where `f` is pinned to `0`). -/

namespace SqueezeBench.Ramsey3.Upper.V002

/-- Numerator and denominator of Shearer's sequence: `f d = (shearer d).1 / (shearer d).2`. -/
def shearer : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | d + 1 => ((shearer d).2 + (d + 1) * d * (shearer d).1, ((d + 1) * (d + 1) + 1) * (shearer d).2)

/-- `⌊(k-1) / f(k-1)⌋ + 1`, the number of vertices that forces a triangle or a `K_k`. -/
def v : SqueezeBench.BoundFn := fun k => (k - 1) * (shearer (k - 1)).2 / (shearer (k - 1)).1 + 1

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Ramsey3.Upper.V001.record v

end SqueezeBench.Ramsey3.Upper.V002
