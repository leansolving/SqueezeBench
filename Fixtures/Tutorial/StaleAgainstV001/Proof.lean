import Fixtures.Tutorial.StaleAgainstV001.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V000.Proof

namespace SqueezeBench.Tutorial.Lower.V001

open SqueezeBench

theorem valid : LowerBoundHolds Tutorial.f record :=
  patch_valid SqueezeBench.Tutorial.Lower.V000.valid (by decide)

theorem improves : ImprovesLower SqueezeBench.Tutorial.Lower.V000.record record :=
  patch_improves (by decide)

theorem strict : StrictlyImprovesLower Tutorial.nMin SqueezeBench.Tutorial.Lower.V000.record record :=
  patch_strict (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V001
