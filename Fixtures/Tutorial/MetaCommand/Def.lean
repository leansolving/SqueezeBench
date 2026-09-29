import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Fixture: Bob's record, but `Proof.lean` runs a metaprogram, which could change the options
without a `set_option`.
`verify` must REJECT it (exit 1). -/

namespace SqueezeBench.Tutorial.Lower.V002

def oddsBound : SqueezeBench.BoundFn := fun m => (m + 1) / 2

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Tutorial.Lower.V001.record oddsBound

end SqueezeBench.Tutorial.Lower.V002
