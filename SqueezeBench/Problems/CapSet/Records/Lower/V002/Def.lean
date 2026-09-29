import SqueezeBench.Problems.CapSet.Records.Lower.V001.Def

/-! Record V002 for CapSet, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Lower/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Lower.V002

-- Cap sizes used on the leftover coordinates: `1, 2, 4, 9, 20` in dimensions `0, …, 4`.
def head (r : ℕ) : ℕ := if r = 1 then 2 else if r = 2 then 4 else if r = 3 then 9 else if r = 4 then 20 else 1

-- A cap of size `45` on every block of 5 coordinates, times `head` on what is left.
def blocks : SqueezeBench.BoundFn :=
  SqueezeBench.pin SqueezeBench.CapSet.nMin (fun n => 45 ^ (n / 5) * head (n % 5))

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.CapSet.Lower.V001.record blocks

end SqueezeBench.CapSet.Lower.V002
