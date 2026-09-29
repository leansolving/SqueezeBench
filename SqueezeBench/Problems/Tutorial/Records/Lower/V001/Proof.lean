import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V000.Proof

/-!
# Tutorial lower-bound record V001 — the three obligations
-/

namespace SqueezeBench.Tutorial.Lower.V001

open SqueezeBench

theorem valid : LowerBoundHolds f record :=
  patch_valid SqueezeBench.Tutorial.Lower.V000.valid (by decide)

theorem improves : ImprovesLower SqueezeBench.Tutorial.Lower.V000.record record :=
  patch_improves (by decide)

theorem strict : StrictlyImprovesLower nMin SqueezeBench.Tutorial.Lower.V000.record record :=
  patch_strict (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V001
