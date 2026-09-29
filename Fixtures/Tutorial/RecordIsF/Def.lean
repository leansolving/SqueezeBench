import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Fixture: a record defined as the problem's own `f`. True, worthless, and unevaluable;
Comparator accepts it, and only the admissibility gate rejects it (exit 1). -/

namespace SqueezeBench.Tutorial.Lower.V002

def record : SqueezeBench.BoundFn := SqueezeBench.Tutorial.f

end SqueezeBench.Tutorial.Lower.V002
