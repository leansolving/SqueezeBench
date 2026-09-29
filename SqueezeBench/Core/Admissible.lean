import Lean
import SqueezeBench.Core.Record

/-!
# Admissibility gates

Mechanical checks on a submitted record function: it must be computable, and its
definition must not reach the problem's `f`. Both keep the record evaluable.

Note `#print axioms` does not catch a reference to `f`: `f` is a definition, not an axiom.

Only the record *function* is checked. Proofs may mention `f` freely.
The fuel-budget gate is wall-clock and lives in `squeeze verify` (`SqueezeBench/Tool/Verify.lean`).
-/

namespace SqueezeBench

open Lean Elab Command

/-- Constants transitively reachable from the declaration of `c`, through types and values. -/
private partial def reachableConsts (env : Environment) (c : Name) (seen : NameSet) :
    NameSet :=
  if seen.contains c then seen
  else
    let seen := seen.insert c
    match env.find? c with
    | some info =>
        info.getUsedConstantsAsSet.toList.foldl (init := seen) fun s c' =>
          reachableConsts env c' s
    | none => seen

/-- Check a record function against the admissibility gates.

```
#check_admissible myRecord avoiding SqueezeBench.Golomb.f
```

Fails if the declaration is `noncomputable`, or if any listed oracle is reachable from its
definition. Silent on success, so it can be left in a submission file as a self-check. -/
elab "#check_admissible " decl:ident "avoiding" oracles:ident,* : command => do
  let env ← getEnv
  let declName ← liftCoreM <| realizeGlobalConstNoOverload decl

  if Lean.isNoncomputable env declName then
    throwError "admissibility gate (computability): `{declName}` is noncomputable, so the \
      record cannot be evaluated."

  let reachable := reachableConsts env declName {}
  for o in oracles.getElems do
    let oracle ← liftCoreM <| realizeGlobalConstNoOverload o
    if reachable.contains oracle then
      throwError "admissibility gate (no oracle reference): the definition of `{declName}` \
        transitively mentions the oracle `{oracle}`. A record must be computable from \
        scratch; only its proofs may refer to the problem's `f`."

end SqueezeBench
