import SqueezeBench.Problems.HypercubeC4.Records.Lower.V003.Def

/-! Record V004 for HypercubeC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V004.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V004

-- V003, improved at `n = 5` by an explicit 55-edge square-free subgraph of `Q₅`.
def record : SqueezeBench.BoundFn :=
  SqueezeBench.patch SqueezeBench.HypercubeC4.Lower.V003.record 5 55

end SqueezeBench.HypercubeC4.Lower.V004
