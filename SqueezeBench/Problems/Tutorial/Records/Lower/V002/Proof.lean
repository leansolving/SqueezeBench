import SqueezeBench.Problems.Tutorial.Records.Lower.V002.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

/-! Record V002 for Tutorial, lower direction, by Pablo Manrique: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Tutorial/Lower/V002.lean`. -/

namespace SqueezeBench.Tutorial.Lower.V002

/-- The set `{1, 3, 4, 5}` witnesses `f 6 ≥ 4`. It is checked, not searched for. -/
theorem four_le_f_six : 4 ≤ SqueezeBench.Tutorial.f 6 := by
  refine SqueezeBench.Tutorial.le_f_of_le_g (by decide) ?_
  have h := SqueezeBench.Tutorial.card_le_g (S := {1, 3, 4, 5}) (m := 6) (by decide) (by decide)
  simpa using h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record :=
  SqueezeBench.patch_valid SqueezeBench.Tutorial.Lower.V001.valid four_le_f_six

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.patch_improves (by decide)

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.patch_strict (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V002
