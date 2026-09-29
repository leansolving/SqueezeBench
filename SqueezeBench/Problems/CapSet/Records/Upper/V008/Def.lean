import SqueezeBench.Problems.CapSet.Records.Upper.V007.Def

/-! Record V008 for CapSet, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V008.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V008

/-- One step of the hyperplane recursion: if every cap in `F₃^(n-1)` has at most `h` points,
then a cap in `F₃ⁿ` has at most `⌊M (3h + 1) / (M + h)⌋` points, `M = 3^(n-1)`
(Bierbrauer–Edel, Davis–Maclagan). -/
def step (M h : ℕ) : ℕ := M * (3 * h + 1) / (M + h)

/-- `chain k` bounds `f (k + 4)`: the exact value `20` at `k = 0`, then one `step` per
dimension. It is `⌊3ⁿ/n⌋`-like: `48, 121, 312, 820, 2187, 5905, …`. -/
def chain : ℕ → ℕ
  | 0 => 20
  | k + 1 => step (3 ^ (k + 4)) (chain k)

/-- The hyperplane-recursion bound at `n`, `chain (n - 4)` (also valid below `n = 4`). -/
def hyperBound (n : ℕ) : ℕ := chain (n - 4)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.CapSet.Upper.V007.record hyperBound

end SqueezeBench.CapSet.Upper.V008
