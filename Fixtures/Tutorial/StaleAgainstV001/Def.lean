import SqueezeBench.Problems.Tutorial.Records.Lower.V000.Def

/-! Fixture: a record written against V000 after V001 was accepted. `verify` must report REBASE
(exit 3), because `Challenges/Tutorial/Lower/V002.lean` exists, before any gate runs. -/

namespace SqueezeBench.Tutorial.Lower.V001

def record : SqueezeBench.BoundFn := SqueezeBench.patch SqueezeBench.Tutorial.Lower.V000.record 5 4

end SqueezeBench.Tutorial.Lower.V001
