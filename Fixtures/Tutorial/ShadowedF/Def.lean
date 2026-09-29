import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Fixture: the record is honest, but `Proof.lean` shadows `f` and proves `valid` for the
shadow. Comparator must reject it (exit 1): the statement does not match the Challenge. -/

namespace SqueezeBench.Tutorial.Lower.V002

def oddsBound : SqueezeBench.BoundFn := fun m => (m + 1) / 2

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Tutorial.Lower.V001.record oddsBound

end SqueezeBench.Tutorial.Lower.V002
