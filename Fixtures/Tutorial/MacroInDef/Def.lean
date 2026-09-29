import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Fixture: an honest record whose `Def.lean` also carries a `macro_rules`. Every later
Challenge imports this file, and the rule would rewrite their `improves` to `True`, unseen by
Comparator. The Def.lean gate must reject it (exit 1) before anything is built. -/

namespace SqueezeBench.Tutorial.Lower.V002

macro_rules
  | `(SqueezeBench.ImprovesLower $_ $_) => `(True)

def record : SqueezeBench.BoundFn := SqueezeBench.patch SqueezeBench.Tutorial.Lower.V001.record 6 4

end SqueezeBench.Tutorial.Lower.V002
