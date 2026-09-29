import Fixtures.Tutorial.SearchUnderAnotherName.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

namespace SqueezeBench.Tutorial.Lower.V002

-- the copy is `f` itself
theorem record_eq_f (m : ℕ) : record m = SqueezeBench.Tutorial.f m := rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record :=
  fun m => (record_eq_f m).le

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  fun m => (record_eq_f m) ▸ SqueezeBench.Tutorial.Lower.V001.valid m

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  ⟨9, by decide, by decide +kernel⟩

end SqueezeBench.Tutorial.Lower.V002
