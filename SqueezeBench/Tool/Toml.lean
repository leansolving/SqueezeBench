import Lake.Toml
import SqueezeBench.Tool.Proc

/-! TOML for the `squeeze` tool: `metadata.toml` of a record and `problem.toml` of a problem, read
with Lake's parser so quoted values with spaces and arrays are handled properly. -/

namespace SqueezeBench.Tool

open Lean

/-- Parse a TOML file; syntax errors are reported with their positions and end with exit 2. -/
def loadTable (path : System.FilePath) : IO Lake.Toml.Table := do
  let contents ← try IO.FS.readFile path
    catch e => infra s!"squeeze: cannot read {path}: {e}"
  let ictx := Parser.mkInputContext contents path.toString
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .ok t => pure t
  | .error log =>
    let msgs ← log.toList.mapM (·.toString)
    infra s!"squeeze: {path} is not valid TOML:\n{"".intercalate msgs}"

/-- A top-level string key; hyphenated keys such as `fuel-budget-heartbeats` are single components. -/
def tomlStr? (t : Lake.Toml.Table) (k : String) : Option String :=
  match t.find? (Name.mkSimple k) with
  | some (.string _ s) => some s
  | _ => none

/-- A top-level non-negative integer key. -/
def tomlNat? (t : Lake.Toml.Table) (k : String) : Option Nat :=
  match t.find? (Name.mkSimple k) with
  | some (.integer _ n) => if n ≥ 0 then some n.toNat else none
  | _ => none

/-- A top-level array-of-strings key; non-string elements are dropped. -/
def tomlStrs? (t : Lake.Toml.Table) (k : String) : Option (Array String) :=
  match t.find? (Name.mkSimple k) with
  | some (.array _ xs) => some (xs.filterMap fun | .string _ s => some s | _ => none)
  | _ => none

/-- A record's `metadata.toml`: what the tree does not already say. `name` is the public
credit, `witness` the `n` at which `strict` holds, `basedOn` the earlier versions whose code the
record reuses; `expect` is the exit code a fixture must produce and is meaningless on a record. -/
structure Metadata where
  name : Option String
  witness : Option Nat
  expect : Option Nat
  basedOn : Array String := #[]

def Metadata.load (path : System.FilePath) : IO Metadata := do
  let t ← loadTable path
  pure { name := tomlStr? t "name", witness := tomlNat? t "witness", expect := tomlNat? t "expect",
         basedOn := (tomlStrs? t "based-on").getD #[] }

/-- The layout `squeeze new` writes; an absent witness becomes a commented placeholder line. -/
def Metadata.render (m : Metadata) : String :=
  let witnessLine := match m.witness with
    | some w => s!"witness = {w}"
    | none => "# witness = <n0>   # uncomment: the n at which your record beats the previous one"
  let basedOnLine := if m.basedOn.isEmpty
    then "# based-on = [\"V001\"]   # uncomment: earlier versions whose code you reuse, e.g. \"V001\" or \"Ramsey/Upper/V002\""
    else s!"based-on = [{", ".intercalate (m.basedOn.map (s!"\"{·}\"")).toList}]"
  "\n".intercalate [s!"name    = \"{m.name.getD ""}\"", witnessLine, basedOnLine, ""]

/-- The trusted per-problem configuration `Challenges/<P>/problem.toml` (docs/ADDING_A_PROBLEM.md). -/
structure ProblemConfig where
  problem : String
  nMin : Nat := 0
  directions : Array String := #[]
  oracles : Array String := #[]
  /-- In the units of `maxHeartbeats`; 200000 is Lean's default for one command. -/
  fuelBudget : Nat := 200000
  /-- The fuel budget also holds for evaluating the record at every `n` from `nMin` to this
  value, so a record that searches for `f` fails at small `n`. -/
  fuelRangeMax : Nat := 100
  /-- The largest `Def.lean` accepted, in bytes; every later Challenge imports it. -/
  maxDefBytes : Nat := 65536
  /-- The largest record directory accepted, in bytes, summed over all its files. -/
  maxRecordBytes : Nat := 1048576

def ProblemConfig.load (path : System.FilePath) : IO ProblemConfig := do
  let t ← loadTable path
  let some problem := tomlStr? t "problem" | infra s!"squeeze: {path} has no `problem` key"
  if (tomlNat? t "fuel-budget-ms").isSome then
    infra s!"squeeze: {path} sets `fuel-budget-ms`; the budget is now `fuel-budget-heartbeats`, in maxHeartbeats units"
  pure { problem, nMin := (tomlNat? t "n-min").getD 0, directions := (tomlStrs? t "directions").getD #[],
         oracles := (tomlStrs? t "oracles").getD #[], fuelBudget := (tomlNat? t "fuel-budget-heartbeats").getD 200000,
         fuelRangeMax := (tomlNat? t "fuel-range-max").getD 100,
         maxDefBytes := (tomlNat? t "max-def-bytes").getD 65536,
         maxRecordBytes := (tomlNat? t "max-record-bytes").getD 1048576 }

/-! ## REPORT.md

A submission carries a `REPORT.md`: how the bound and its proofs were obtained, and the setup
used. The reviewer reads it; no gate checks it. -/

/-- The `REPORT.md` that `squeeze new` writes. -/
def reportTemplate (problem direction version name : String) : String := s!"# {problem}, {direction} record, {version}

By {name}.

## How the bound was obtained

The idea behind the bound, and the sources it comes from (papers, known constructions, tables).

## How the proofs were obtained

How `valid`, `improves` and `strict` were proved: by hand, with an AI agent, with automation;
which parts were hard, and what was tried and abandoned.

## Sources

Every outside source of code or data: the URL, pinned to a commit or a version, the license, and
what was taken (CONTRIBUTING, *License and outside sources*). Write *None* if there is none.

## Setup

- Tools: the models and agents used (name and version), if any, and other software.
- Machine: CPU, memory, operating system.
- Time spent, and any computation that ran outside Lean (for example a search that found a
  construction).
"

end SqueezeBench.Tool
