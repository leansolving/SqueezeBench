import Fixtures.Tutorial.MacroInDef.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

namespace SqueezeBench.Tutorial.Lower.V002

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record :=
  SqueezeBench.patch_valid SqueezeBench.Tutorial.Lower.V001.valid (by decide)

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  trivial

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.patch_strict (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V002
