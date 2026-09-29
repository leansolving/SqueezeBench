import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

/-! Fixture: a record that is `f` under another name, an exhaustive search over the subsets of
`{1, …, m}`. It is computable, reaches no oracle and is cheap at its witness, so every other gate
passes it; only the range part of the fuel gate rejects it (exit 1). -/

namespace SqueezeBench.Tutorial.Lower.V002

-- the definition of `g`, copied under a new name so that it reaches no oracle
def search (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).powerset.filter (fun S => ∀ x ∈ S, 2 * x ∉ S)).sup Finset.card

def record : SqueezeBench.BoundFn := fun m => if m < 1 then 0 else search m

end SqueezeBench.Tutorial.Lower.V002
