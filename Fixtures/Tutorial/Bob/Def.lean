import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Fixture: an honest record that folds in the odd-numbers bound `⌈m/2⌉` with `maxWith`.
`verify` must ACCEPT it (exit 0). -/

namespace SqueezeBench.Tutorial.Lower.V002

def oddsBound : SqueezeBench.BoundFn := fun m => (m + 1) / 2

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Tutorial.Lower.V001.record oddsBound

end SqueezeBench.Tutorial.Lower.V002
