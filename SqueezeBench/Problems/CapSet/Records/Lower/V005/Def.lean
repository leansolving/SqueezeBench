import SqueezeBench.Problems.CapSet.Records.Lower.V004.Def

/-! Record V005 for CapSet, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Lower/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Lower.V005

-- The extended product construction (Edel 2004, Tyrrell 2023) with the admissible set
-- `I(m, m-1)` and the extendable collection of sizes `(12, 112, 112)` in `F₃⁶`: a cap of
-- size `m · 12 · 112 ^ (m - 1)` in dimension `6 m`.
def fam (m : ℕ) : ℕ := m * (12 * 112 ^ (m - 1))

-- Given `[b (k-1), …, b 0]`, the best product of a table cap or a family cap with an earlier `b`.
def step (prev : List ℕ) : ℕ :=
  (List.range (prev.length / 6)).foldl
    (fun acc i => max acc (fam (i + 1) * prev.getD (6 * (i + 1) - 1) 0))
    (SqueezeBench.CapSet.Lower.V004.tbl.foldl
      (fun acc p => max acc (p.2 * prev.getD (p.1 - 1) 0)) 0)

-- `dp n = [b n, b (n-1), …, b 0]` with `b 0 = 1`.
def dp : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => step (dp k) :: dp k

def best (n : ℕ) : ℕ := (dp n).headD 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.CapSet.Lower.V004.record
    (SqueezeBench.pin SqueezeBench.CapSet.nMin best)

end SqueezeBench.CapSet.Lower.V005
