import Lean
import SqueezeBench.Tool.Proc

/-! `squeeze budget-probe`: the computation budget of a record's `Proof.lean` (docs/CONTRIBUTING.md, Computation budget).
A proof reasons; computation may only check data the record provides. Two limits enforce this:
every declaration runs under `proofDeclHeartbeats`, and the heartbeats of the whole file sum to
at most `proofTotalHeartbeats`, so a search split into many small lemmas is caught too.

The probe elaborates the file itself, command by command, with `Elab.async` off: only then does
the kernel check each declaration on this thread, where `IO.getNumHeartbeats` sees its work. The
file may therefore not change these options, nor run code that could: `set_option` is limited to
`linter.*` and `pp.*`, metaprogramming commands are refused, and so are attributes that register
code. `squeeze verify` runs the probe sandboxed, since elaborating untrusted source runs its
tactics. -/

namespace SqueezeBench.Tool.Budget

open SqueezeBench.Tool
open System (FilePath)
open Lean (Json Name Syntax)

/-- The heartbeat limit of each declaration of `Proof.lean`, in `maxHeartbeats` units: Lean's default. -/
def proofDeclHeartbeats : Nat := 200000

/-- The heartbeats of the whole `Proof.lean`, summed over its commands, in `maxHeartbeats` units. -/
def proofTotalHeartbeats : Nat := 200000

def usage : String := "\
usage: lake exe squeeze budget-probe <Proof.lean> [--measure-only]

Elaborates the file with `Elab.async` off and each declaration limited to the per-declaration
budget, and prints the heartbeats of each command and their total as JSON. Exit 1 if the file
sets a forbidden option, uses a forbidden command or attribute, or fails to elaborate.
--measure-only skips the syntax restriction and the per-declaration limit, leaving the file's own
`set_option`s in force: it measures what a proof costs, for calibration, and judges nothing."

/-- A `set_option` the file may use: presentation and linting only. -/
def optionAllowed (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "linter." || s.startsWith "pp."

/-- Top-level commands a `Proof.lean` may contain; `set_option` and `in` are checked apart. -/
def commandsAllowed : List Name :=
  [``Lean.Parser.Command.declaration, `lemma, ``Lean.Parser.Command.namespace,
   ``Lean.Parser.Command.end, ``Lean.Parser.Command.section, ``Lean.Parser.Command.open,
   ``Lean.Parser.Command.variable, ``Lean.Parser.Command.universe, ``Lean.Parser.Command.include,
   ``Lean.Parser.Command.omit, ``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.attribute,
   ``Lean.Parser.Command.mutual]

/-- Attributes that only tag a declaration for existing automation; `Attr.simple` covers
`tactic`, `init`, `implemented_by` and the like, so its names are listed one by one. -/
def attrKindsAllowed : List Name :=
  [``Lean.Parser.Attr.simp, ``Lean.Parser.Attr.instance, ``Lean.Parser.Attr.ext]

def simpleAttrsAllowed : List String := ["reducible", "irreducible", "semireducible", "inline"]

/-- The syntax kinds that run user code wherever they occur. -/
def kindsForbidden : List Name := [``Lean.Parser.Tactic.runTac, `Lean.byElab]

private def kindTail (k : Name) : String := k.components.getLast!.toString

/-- The first identifier among a node's children: the option of a `set_option`, the name of a simple attribute. -/
private def firstIdent (stx : Syntax) : Option Name :=
  stx.getArgs.findSome? fun a => if a.isIdent then some a.getId else none

/-- What the syntax restriction refuses in one syntax tree, if anything. -/
partial def forbiddenIn (stx : Syntax) : Option String :=
  let k := stx.getKind
  if k == ``Lean.Parser.Command.set_option || k == ``Lean.Parser.Tactic.set_option
      || k == ``Lean.Parser.Term.set_option then
    match firstIdent stx with
    | some n => if optionAllowed n then none
      else some s!"`set_option {n}` (only `linter.*` and `pp.*` options may be set; the budget is fixed)"
    | none => some "a `set_option` without an option name"
  else if kindsForbidden.contains k then some s!"`{kindTail k}`, which runs code during elaboration"
  else if k == ``Lean.Parser.Attr.simple then
    match firstIdent stx with
    | some n => if simpleAttrsAllowed.contains n.toString then none
      else some s!"the attribute `{n}` (allowed: simp, instance, ext, {", ".intercalate simpleAttrsAllowed})"
    | none => none
  else if k.toString.startsWith "Lean.Parser.Attr." && !attrKindsAllowed.contains k then
    some s!"the attribute `{kindTail k}` (allowed: simp, instance, ext, {", ".intercalate simpleAttrsAllowed})"
  else stx.getArgs.findSome? forbiddenIn

/-- The command-level restriction: an allowed command kind, `in` on both sides, then the whole tree. -/
partial def forbiddenCommand (stx : Syntax) : Option String :=
  let k := stx.getKind
  if k == ``Lean.Parser.Command.in then (forbiddenCommand stx[0]).orElse fun _ => forbiddenCommand stx[2]
  else if k == ``Lean.Parser.Command.set_option then forbiddenIn stx
  else if !commandsAllowed.contains k then some s!"the command `{kindTail k}` (a Proof.lean holds declarations, not metaprograms)"
  else forbiddenIn stx

/-- A label for a command in the report: the declared name if there is one, else its kind. -/
partial def commandLabel (stx : Syntax) : String :=
  let rec declName (s : Syntax) : Option Name :=
    if s.getKind == ``Lean.Parser.Command.declId then some s[0].getId
    else s.getArgs.findSome? declName
  match declName stx with
  | some n => n.toString
  | none => kindTail stx.getKind

private def reportErrors (msgs : Lean.MessageLog) : IO Unit := do
  for m in msgs.toList do
    if m.severity == .error then IO.eprint (← m.toString)

/-- Elaborate `file` command by command, measuring the heartbeats of each; print the JSON report. -/
unsafe def probe (file : FilePath) (measureOnly : Bool) : IO Unit := do
  let text ← IO.FS.readFile file
  let ictx := Lean.Parser.mkInputContext text file.toString
  let (header, pstate, msgs) ← Lean.Parser.parseHeader ictx
  if msgs.hasErrors then reportErrors msgs; reject s!"{file}: the header does not parse"
  let opts : Lean.Options :=
    let o := Lean.Options.empty.setBool `Elab.async false
    if measureOnly then o.set `maxHeartbeats (0 : Nat) else o.set `maxHeartbeats proofDeclHeartbeats
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let (env, msgs) ← Lean.Elab.processHeader header opts msgs ictx
  if msgs.hasErrors then reportErrors msgs; infra s!"{file}: the imports do not load (build them first)"
  let mut cmdState := Lean.Elab.Command.mkState env msgs opts
  let mut pstate := pstate
  let mut rows : Array (String × Nat × Nat) := #[]
  let mut total := 0
  repeat
    let scope := cmdState.scopes.head!
    let pmctx : Lean.Parser.ParserModuleContext :=
      { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (stx, ps, msgs') := Lean.Parser.parseCommand ictx pmctx pstate cmdState.messages
    pstate := ps
    cmdState := { cmdState with messages := msgs' }
    if msgs'.hasErrors then reportErrors msgs'; reject s!"{file} does not parse"
    if Lean.Parser.isTerminalCommand stx then break
    let line := (ictx.fileMap.toPosition ((stx.getPos?).getD 0)).line
    unless measureOnly do
      if let some what := forbiddenCommand stx then
        reject s!"{file}:{line}: {what}"
    let ctx : Lean.Elab.Command.Context :=
      { cmdPos := (stx.getPos?).getD 0, fileName := ictx.fileName, fileMap := ictx.fileMap,
        snap? := none, cancelTk? := none }
    let before ← IO.getNumHeartbeats
    match ← (EIO.toIO' ((Lean.Elab.Command.elabCommandTopLevel stx ctx).run cmdState)) with
    | .ok (_, st) => cmdState := st
    | .error e => reject s!"{file}:{line}: {← e.toMessageData.toString}"
    let used := ((← IO.getNumHeartbeats) - before) / 1000
    total := total + used
    rows := rows.push (commandLabel stx, line, used)
    if cmdState.messages.hasErrors then
      reportErrors cmdState.messages
      reject s!"{file}:{line}: `{commandLabel stx}` does not elaborate within {proofDeclHeartbeats} heartbeats and the fixed options"
  let cmds := rows.map fun (label, line, hb) =>
    Json.mkObj [("command", label), ("line", line), ("heartbeats", hb)]
  IO.println (Json.mkObj [("file", file.toString), ("total", total), ("commands", Json.arr cmds)]).compress

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | ["-h"] | ["--help"] => IO.println usage; pure 0
  | [f] => probe f false; pure 0
  | [f, "--measure-only"] => probe f true; pure 0
  | _ => infra usage

end SqueezeBench.Tool.Budget
