import Fixtures.Tutorial.RecordIsF.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

namespace SqueezeBench.Tutorial.Lower.V002

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record := fun _ => Nat.le_refl _

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.Tutorial.Lower.V001.valid

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  ⟨9, by decide, by decide +kernel⟩

end SqueezeBench.Tutorial.Lower.V002
