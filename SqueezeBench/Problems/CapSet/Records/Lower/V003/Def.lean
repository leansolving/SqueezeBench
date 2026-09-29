import SqueezeBench.Problems.CapSet.Records.Lower.V002.Def

/-! Record V003 for CapSet, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Lower/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Lower.V003

-- Cap sizes used on the leftover coordinates: `1, 2, 4, 9, 20, 45` in dimensions `0, …, 5`.
def head (r : ℕ) : ℕ :=
  if r = 1 then 2 else if r = 2 then 4 else if r = 3 then 9 else if r = 4 then 20
  else if r = 5 then 45 else 1

-- A cap of size `112` on every block of 6 coordinates, times `head` on what is left.
def blocks : SqueezeBench.BoundFn :=
  SqueezeBench.pin SqueezeBench.CapSet.nMin (fun n => 112 ^ (n / 6) * head (n % 6))

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.CapSet.Lower.V002.record blocks

end SqueezeBench.CapSet.Lower.V003
