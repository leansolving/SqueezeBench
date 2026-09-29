import SqueezeBench.Problems.CapSet.Records.Lower.V000.Def

/-! Record V001 for CapSet, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Lower/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Lower.V001

-- Cap sizes used on the leftover coordinates: `1, 2, 4, 9` in dimensions `0, 1, 2, 3`.
def head (r : ℕ) : ℕ := if r = 1 then 2 else if r = 2 then 4 else if r = 3 then 9 else 1

-- A cap of size `20` on every block of four coordinates, times `head` on what is left.
def blocks : SqueezeBench.BoundFn :=
  SqueezeBench.pin SqueezeBench.CapSet.nMin (fun n => 20 ^ (n / 4) * head (n % 4))

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.CapSet.Lower.V000.record blocks

end SqueezeBench.CapSet.Lower.V001
