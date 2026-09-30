import Lean
import SqueezeBench.Tool.Toml
import SqueezeBench.Tool.Tree
import SqueezeBench.Tool.Budget

/-! `squeeze verify`: the rebase check and the six admission gates (docs/CONTRIBUTING.md) for one record
directory, pending on a pull request or accepted on `main`, or for a fixture. Linux only:
Comparator sandboxes with landrun, which needs Landlock, and it must not run as root. Tools
come from `.tools/` (built by `squeeze bootstrap`) unless a `COMPARATOR_*` or `SQUEEZE_LANDRUN_BIN`
variable overrides them. -/

namespace SqueezeBench.Tool.Verify

open SqueezeBench.Tool
open System (FilePath)
open Lean (Json Name Syntax)

def usage : String := "\
usage: lake exe squeeze verify <record-dir> [--base <ref>] [--accepted]

<record-dir> is SqueezeBench/Problems/<P>/Records/<Dir>/V<k> or Fixtures/<P>/<Name>. Runs the
rebase check and the six gates: the diff restriction (only with --base), the size limits and
the Def.lean restriction, Comparator (at most 30 min and 16 GB), the computation budget of
Proof.lean (heartbeats per declaration and in all), admissibility, and the fuel
budget (heartbeats and memory of `decide +kernel` at the witness, and of evaluating the record at
every n from nMin to fuel-range-max). --accepted skips the rebase check (the directory is an
accepted record; `squeeze audit` passes it). Exit 0 ACCEPT, 1 REJECT,
3 rebase needed, 2 when the tools or arguments are wrong."

/-- A judged rejection of the record (exit 1). -/
def die (msg : String) : IO α := reject s!"REJECT: {msg}"

/-- A problem with the verifier itself, not the record (exit 2). -/
def fail (msg : String) : IO α := infra s!"squeeze verify: {msg}"

/-- The verifier binaries; the sandbox wrapper, never bare landrun, is what Comparator gets. -/
structure Tools where
  comparator : String
  lean4export : String
  nanoda : String
  landrunBin : String
  landrun : String

def Tools.resolve (root : FilePath) : IO Tools := do
  let get (var : String) (default : FilePath) : IO String := do
    let p := (← IO.getEnv var).getD default.toString
    unless ← (FilePath.mk p).pathExists do
      fail s!"{var} is unset or missing ({p}); run `lake exe squeeze bootstrap`"
    pure p
  let bin := root / ".tools" / "bin"
  let t : Tools := {
    comparator := ← get "COMPARATOR_BIN" (bin / "comparator"),
    lean4export := ← get "COMPARATOR_LEAN4EXPORT" (bin / "lean4export"),
    nanoda := ← get "COMPARATOR_NANODA" (bin / "nanoda_bin"),
    landrunBin := ← get "SQUEEZE_LANDRUN_BIN" (bin / "landrun"),
    landrun := ← get "COMPARATOR_LANDRUN" (root / "scripts" / "landrun-wrapper.sh") }
  if t.landrun.endsWith "/landrun" then
    fail "COMPARATOR_LANDRUN must be the wrapper (scripts/landrun-wrapper.sh), not landrun itself: bare landrun swallows lean4export's -- separator"
  pure t

def Tools.envPairs (t : Tools) : Array (String × String) :=
  #[("COMPARATOR_LANDRUN", t.landrun), ("COMPARATOR_LEAN4EXPORT", t.lean4export),
    ("COMPARATOR_NANODA", t.nanoda), ("SQUEEZE_LANDRUN_BIN", t.landrunBin)]

/-- The export is only meaningful on identical .olean headers, so every verifier package must target our toolchain. -/
def checkToolchains : IO String := do
  let ours := (← IO.FS.readFile "lean-toolchain").trimS
  for pkg in ["Comparator", "lean4export"] do
    let f := FilePath.mk ".lake" / "packages" / pkg / "lean-toolchain"
    unless ← f.pathExists do fail s!"{f} missing; run `lake exe squeeze bootstrap`"
    let theirs := (← IO.FS.readFile f).trimS
    unless theirs == ours do
      fail s!"lean-toolchain is {ours} but {pkg} targets {theirs} — bump the Comparator rev in lakefile.toml"
  pure ours

/-- The revision `.tools/stamp` records for `key`, as `key=<rev>` lines written by bootstrap. -/
private def stampRev (root : FilePath) (key : String) : IO (Option String) := do
  let f := root / ".tools" / "stamp"
  unless ← f.pathExists do return none
  let pre := key ++ "="
  let line? := (← IO.FS.lines f).find? (·.startsWith pre)
  pure (line?.map fun l => (l.dropS pre.length).trimS)

/-- A tool in `.tools/bin` built at a revision other than the manifest's pin is stale. -/
def checkManifestFresh (root : FilePath) (t : Tools) : IO Unit := do
  let binDir := (root / ".tools" / "bin").toString ++ "/"
  for (path, key, pkg) in [(t.comparator, "comparator", "Comparator"), (t.lean4export, "lean4export", "lean4export")] do
    if path.startsWith binDir then
      let pinned ← manifestRev pkg
      let built := (← stampRev root key).getD "none"
      unless built == pinned do
        fail s!"{key} in .tools/ was built at {built} but lake-manifest.json pins {pinned}; run `lake exe squeeze bootstrap`"

def checkHost : IO Unit := do
  if System.Platform.isWindows || System.Platform.isOSX then
    fail "Linux only: Comparator sandboxes with landrun, which needs Landlock"
  if ← isRoot then fail "must not run as root (Comparator trust assumption 6)"

private def shortSha (pkg : String) : IO String := do
  let out ← run { cmd := "git", args := #["rev-parse", "--short", "HEAD"],
                  cwd := some (FilePath.mk ".lake" / "packages" / pkg) }
  pure (if out.exitCode == 0 then out.stdout.trimS else "?")

structure Args where
  dir : String := ""
  base : Option String := none
  accepted : Bool := false

def parseArgs : List String → Args → Except String Args
  | [], a => if a.dir.isEmpty then .error usage else .ok a
  | "--accepted" :: rest, a => parseArgs rest { a with accepted := true }
  | "--base" :: b :: rest, a => if b.startsWith "--" then .error "--base needs a git ref" else parseArgs rest { a with base := some b }
  | ["--base"], _ => .error "--base needs a git ref"
  | d :: rest, a => if d.startsWith "-" || !a.dir.isEmpty then .error usage else parseArgs rest { a with dir := normalizeDir d }

/-! ## Gate 2: the Def.lean restriction, checked by parsing alone

`Def.lean` is what the next Challenge imports, so it may contain only commands that cannot
change how an importing file elaborates: `def` and `abbrev` without modifiers or attributes,
plus doc comments, `open`, `set_option` and the `namespace … end` pair. It is parsed, never
elaborated: a declaration's body is untrusted code and Comparator must be the first to build
it. Only the scope commands are elaborated, so that `open` activates the scoped notation a
body may use; they run no user code. -/

inductive DefSlot where
  | scope
  | decl (name : Name)
  | doc
  | reject (what : String)
  deriving Inhabited

private def kindTail (k : Name) : String := k.components.getLast!.toString

/-- Classify one parsed command of `Def.lean`. -/
partial def classifyDef (stx : Syntax) : DefSlot :=
  let k := stx.getKind
  if k == ``Lean.Parser.Command.declaration then
    -- declModifiers: docComment? attributes? visibility? protected? (meta|noncomputable)? unsafe? (partial|nonrec)?
    let mods := stx[0]
    if !mods[1].isNone then .reject "an attribute"
    else if (List.range 5).any (fun i => !mods[i + 2].isNone) then .reject "a declaration modifier"
    else
      let inner := stx[1]
      if inner.getKind == ``Lean.Parser.Command.definition then
        if !inner[4].isNone then .reject "a `deriving` clause"
        else .decl inner[1][0].getId
      else if inner.getKind == ``Lean.Parser.Command.abbrev then .decl inner[1][0].getId
      else .reject s!"a `{kindTail inner.getKind}` declaration"
  else if k == ``Lean.Parser.Command.«in» then
    match classifyDef stx[0], classifyDef stx[2] with
    | .scope, r => r
    | _, _ => .reject "an `in` prefix that is not `open` or `set_option`"
  else if k == ``Lean.Parser.Command.«namespace» || k == ``Lean.Parser.Command.«end»
      || k == ``Lean.Parser.Command.«open» || k == ``Lean.Parser.Command.«set_option» then .scope
  else if k == ``Lean.Parser.Command.moduleDoc then .doc
  else .reject s!"a `{kindTail k}` command"

/-- The source-size limits of `problem.toml`: `Def.lean`, and every file of the directory together. -/
def gateSize (cfg : ProblemConfig) (dir : FilePath) : IO Unit := do
  let defBytes := (← (dir / "Def.lean").metadata).byteSize.toNat
  if defBytes > cfg.maxDefBytes then
    die s!"{dir / "Def.lean"} is {defBytes} bytes; the limit is {cfg.maxDefBytes} (problem.toml: max-def-bytes)"
  let mut total := 0
  for p in ← dir.walkDir do
    if !(← p.isDir) then total := total + (← p.metadata).byteSize.toNat
  if total > cfg.maxRecordBytes then
    die s!"{dir} holds {total} bytes; the limit is {cfg.maxRecordBytes} (problem.toml: max-record-bytes)"
  note s!"Def.lean {defBytes} bytes (limit {cfg.maxDefBytes}), record {total} bytes (limit {cfg.maxRecordBytes})"

/-- The modules `Def.lean` may import: the trusted spine and the predecessor's definition. -/
def importAllowed (t : Track) (k : Nat) (m : Name) : Bool :=
  let s := m.toString
  s == "Init" || s.startsWith "Init." || s == "Lean" || s.startsWith "Lean." || s == "Std" || s.startsWith "Std."
  || s == "Mathlib" || s.startsWith "Mathlib."
  || s == "SqueezeBench.Core" || s.startsWith "SqueezeBench.Core."
  || s == s!"SqueezeBench.Problems.{t.problem}.Def" || s == s!"SqueezeBench.Problems.{t.problem}.Finite"
  || (k > 0 && s == t.recordModule (k - 1) ++ ".Def")

private def reportErrors (msgs : Lean.MessageLog) : IO Unit := do
  for m in msgs.toList do
    if m.severity == .error then IO.eprint (← m.toString)

unsafe def gateDef (t : Track) (k : Nat) (defFile : FilePath) : IO Unit := do
  let text ← IO.FS.readFile defFile
  let ictx := Lean.Parser.mkInputContext text defFile.toString
  let (header, pstate, msgs) ← Lean.Parser.parseHeader ictx
  if msgs.hasErrors then reportErrors msgs; die s!"{defFile}: the header does not parse"
  if Lean.Elab.HeaderSyntax.isModule header then die s!"{defFile} must not be a `module`"
  let imports : Array Lean.Import := Lean.Elab.HeaderSyntax.imports header (includeInit := false)
  for i in imports do
    if i.importAll || i.isMeta || !importAllowed t k i.module then
      die s!"{defFile} imports {i.module}; a Def.lean may import only Lean, Mathlib, SqueezeBench.Core, {t.problem}'s Def and Finite, and the previous record's Def"
  -- the imports are trusted, so building them is not compiling the record (Comparator assumption 2)
  for i in imports do
    if i.module.toString.startsWith "SqueezeBench." then
      let out ← run { cmd := "lake", args := #["build", i.module.toString] }
      if out.exitCode != 0 then fail s!"lake build {i.module} failed:\n{out.stderr.trimEndS}"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let (env, msgs) ← Lean.Elab.processHeader header {} msgs ictx
  if msgs.hasErrors then reportErrors msgs; fail s!"{defFile}: the imports do not load"
  let mut cmdState := Lean.Elab.Command.mkState env msgs {}
  let mut pstate := pstate
  let mut sawRecord := false
  let mut opened := false
  repeat
    let scope := cmdState.scopes.head!
    let pmctx : Lean.Parser.ParserModuleContext :=
      { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (stx, ps, msgs') := Lean.Parser.parseCommand ictx pmctx pstate cmdState.messages
    pstate := ps
    cmdState := { cmdState with messages := msgs' }
    if msgs'.hasErrors then reportErrors msgs'; die s!"{defFile} does not parse"
    if Lean.Parser.isTerminalCommand stx then break
    match classifyDef stx with
    | .scope =>
      if stx.getKind == ``Lean.Parser.Command.«namespace» then
        let n := stx[1].getId.toString
        unless n == t.ns k do die s!"{defFile} opens namespace {n}; expected {t.ns k}"
        opened := true
      let ctx : Lean.Elab.Command.Context :=
        { cmdPos := (stx.getPos?).getD 0, fileName := ictx.fileName, fileMap := ictx.fileMap,
          snap? := none, cancelTk? := none }
      match ← (EIO.toIO' ((Lean.Elab.Command.elabCommandTopLevel stx ctx).run cmdState)) with
      | .ok (_, st) => cmdState := st
      | .error e => fail s!"{defFile}: {← e.toMessageData.toString}"
      if cmdState.messages.hasErrors then reportErrors cmdState.messages; die s!"{defFile}: a scope command fails"
    | .decl n =>
      if n == `record && opened && scope.currNamespace.toString == t.ns k then sawRecord := true
    | .doc => pure ()
    | .reject what => die s!"{defFile} contains {what}; a Def.lean may hold only plain `def` and `abbrev` (docs/CONTRIBUTING.md)"
  unless sawRecord do die s!"{defFile} does not declare `record` inside `namespace {t.ns k}`"
  note s!"Def.lean holds only plain definitions; imports {imports.map (·.module.toString) |>.toList}"

/-! ## Gates 3–6 -/

/-- A wall-clock limit on the whole Comparator run: build, export and both kernels. -/
def comparatorTimeoutSec : Nat := 1800

/-- The memory limit of the whole Comparator run in MB, swap excluded; enforced only under systemd. -/
def comparatorMemoryMb : Nat := 16384

/-- How a limited run ended: its exit code and captured output, or stopped by a limit. -/
inductive Limited where
  | exited (code : UInt32) (out : String)
  | timeout
  | oom

/-- Run `cmd args` in `root` with the environment `env` under a wall-clock and a memory limit
(swap excluded), as a transient systemd unit when systemd is available. Output streams to the
terminal unless `capture`, in which case stdout is returned (stderr still streams). Without
systemd only the wall-clock limit applies, and output is always captured. -/
def runLimited (root : FilePath) (name : String) (cmd : String) (args : Array String)
    (env : Array (String × String)) (timeoutSec memoryMb : Nat) (capture : Bool)
    (props : Array String := #[]) : IO Limited := do
  if (← findOnPath "systemd-run").isSome && (← IO.getEnv "XDG_RUNTIME_DIR").isSome then
    let unit := s!"squeeze-{name}-{← IO.Process.getPID}"
    let mut sargs := props ++ #["--user", "--pipe", "--quiet", s!"--unit={unit}",
                      s!"--property=RuntimeMaxSec={timeoutSec}",
                      s!"--property=MemoryMax={memoryMb}M", "--property=MemorySwapMax=0"]
    for (k, v) in env do sargs := sargs ++ #["-E", s!"{k}={v}"]
    sargs := sargs ++ #["--working-directory", root.toString, "--", cmd] ++ args
    let (code, out) ← if capture then do
        let child ← try IO.Process.spawn { cmd := "systemd-run", args := sargs, stdout := .piped }
          catch e => infra s!"squeeze: cannot run systemd-run: {e}"
        let out ← child.stdout.readToEnd
        pure (← child.wait, out)
      else pure (← runInherit { cmd := "systemd-run", args := sargs }, "")
    if code != 0 then
      -- a failed unit stays loaded, so systemd can say whether a limit stopped it
      let res := (← run { cmd := "systemctl", args := #["--user", "show", unit, "-p", "Result", "--value"] }).stdout.trimS
      let _ ← run { cmd := "systemctl", args := #["--user", "reset-failed", unit] }
      if res == "timeout" then return .timeout
      if res == "oom-kill" then return .oom
    pure (.exited code out)
  else
    note s!"systemd-run unavailable; running {name} without the memory limit{if props.isEmpty then "" else " or the extra restrictions"}"
    let (res, out) ← outputWithTimeout
      { cmd, args, cwd := some root, env := env.map fun (k, v) => (k, some v) } (timeoutSec * 1000)
    match res with
    | none => pure .timeout
    | some code =>
      unless capture do IO.print out
      pure (.exited code out)

/-- Gate 3: Comparator, on a copy of the version's config naming this module as the solution. -/
def gateComparator (root : FilePath) (cfgFile : FilePath) (tools : Tools) (module : String) : IO Unit := do
  let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgFile))
  let cfg := cfg.setObjVal! "solution_module" (.str module)
  IO.FS.withTempFile fun h cfgPath => do
    h.putStr cfg.pretty
    h.flush
    let env := #[("PATH", (← IO.getEnv "PATH").getD ""), ("HOME", (← IO.getEnv "HOME").getD "")] ++ tools.envPairs
    match ← runLimited root "comparator" "lake" #["env", tools.comparator, cfgPath.toString] env
        comparatorTimeoutSec comparatorMemoryMb (capture := false)
        (props := #["--property=RestrictAddressFamilies=~AF_UNIX"]) with
    | .exited 0 _ => pure ()
    | .exited _ _ => die "Comparator rejected the record"
    | .timeout => die s!"Comparator did not finish within {comparatorTimeoutSec}s"
    | .oom => die s!"Comparator exceeded {comparatorMemoryMb} MB of memory"

/-- A wall-clock guard on the budget probe; heartbeats bound the work, this only catches a hang. -/
def budgetTimeoutSec : Nat := 1800

/-- The memory limit of the budget probe in MB: heartbeats do not bound what the kernel allocates. -/
def budgetMemoryMb : Nat := 8192

/-- Gate 4: `Proof.lean` keeps to the computation budget (`Budget.lean`). The probe elaborates the
record's source, which runs its tactics, so it runs under landrun with the whole filesystem
read-only, and under the memory limit. -/
def gateBudget (root : FilePath) (tools : Tools) (proof : FilePath) : IO Unit := do
  let squeeze := (← IO.appPath).toString
  let env := #[("LEAN_PATH", (← IO.getEnv "LEAN_PATH").getD ""),
               ("LEAN_SYSROOT", (← IO.getEnv "LEAN_SYSROOT").getD ""),
               ("SQUEEZE_LANDRUN_BIN", tools.landrunBin)]
  let args := #["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec",
                "--env", "LEAN_PATH", "--env", "LEAN_SYSROOT", squeeze, "budget-probe", proof.toString]
  match ← runLimited root "budget" tools.landrun args env budgetTimeoutSec budgetMemoryMb (capture := true) with
  | .timeout => die s!"the budget probe did not finish within {budgetTimeoutSec}s"
  | .oom => die s!"{proof} exceeded {budgetMemoryMb} MB of memory while elaborating"
  | .exited 1 _ => die s!"{proof} breaks the computation budget (the reason is above; docs/CONTRIBUTING.md)"
  | .exited 0 out =>
    let some line := (out.splitOn "\n").reverse.find? (·.startsWith "{")
      | fail s!"the budget probe printed no report:\n{out}"
    let json ← IO.ofExcept (Json.parse line)
    let total ← IO.ofExcept (json.getObjValAs? Nat "total")
    let cmds ← IO.ofExcept (json.getObjValAs? (Array Json) "commands")
    let rows := cmds.filterMap fun c => match c.getObjValAs? String "command", c.getObjValAs? Nat "heartbeats" with
      | .ok n, .ok h => some (n, h)
      | _, _ => none
    let top := (rows.qsort (fun a b => a.2 > b.2)).toList.take 5
    let topStr := ", ".intercalate (top.map fun (n, h) => s!"{n} {h}")
    if total > Budget.proofTotalHeartbeats then
      die s!"{proof} uses {total} heartbeats in all; the limit is {Budget.proofTotalHeartbeats} (heaviest: {topStr})"
    note s!"{total} heartbeats in all (limit {Budget.proofTotalHeartbeats}; each declaration at most {Budget.proofDeclHeartbeats}); heaviest: {topStr}"
  | .exited c _ => fail s!"the budget probe failed (exit {c})"

/-- Gate 5: the record is computable and its definition reaches no oracle. -/
def gateAdmissible (probe : FilePath) (cfg : ProblemConfig) (module recordConst : String) : IO Unit := do
  if cfg.oracles.isEmpty then die s!"{cfg.problem}'s problem.toml lists no oracles"
  note s!"oracles from trusted config: {", ".intercalate cfg.oracles.toList}"
  IO.FS.writeFile probe s!"import {module}\n#check_admissible {recordConst} avoiding {", ".intercalate cfg.oracles.toList}\n"
  let code ← runInherit { cmd := ← leanBin, args := #[probe.toString] }
  if code != 0 then die "record failed the admissibility gates"
  note "record is computable and reaches no oracle"

/-- A wall-clock guard on each fuel probe; heartbeats and memory bound the work, this only catches a hang. -/
def fuelGuardMs : Nat := 600000

/-- The memory limit of each fuel probe in MB (`lean -M`); the probe alone peaks at 6.6 GB with Mathlib loaded. -/
def fuelMemoryMb : Nat := 8192

/-- Gate 6: `decide +kernel` must settle the witness comparison within the problem's heartbeat
budget and `fuelMemoryMb`. Heartbeats count work, not time, so the verdict does not depend on
the machine. -/
def gateFuel (probe : FilePath) (t : Track) (cfg : ProblemConfig)
    (module prevConst recordConst : String) (witness : Nat) : IO Unit := do
  let budget := cfg.fuelBudget
  let cmp := if t.isLower then "<" else ">"
  IO.FS.writeFile probe s!"import {module}
-- The next submitter settles this in the kernel, not by `#eval`; `maxHeartbeats` bounds the work.
set_option maxHeartbeats {budget} in
example : {prevConst} {witness} {cmp} {recordConst} {witness} := by decide +kernel
"
  let (res, out) ← outputWithTimeout
    { cmd := ← leanBin, args := #["-M", toString fuelMemoryMb, probe.toString] } fuelGuardMs
  unless out.trimS.isEmpty do IO.print out
  match res with
  | some 0 =>
    note s!"`decide +kernel` settles the witness comparison within {budget} heartbeats and {fuelMemoryMb} MB"
  | none =>
    die s!"the fuel probe at witness {witness} did not finish within {fuelGuardMs / 1000}s"
  | some _ =>
    -- `decide` prints "is false" only when it evaluated the comparison to false
    if (out.splitOn "is false").length > 1 then
      die s!"the witness comparison is false at {witness}; metadata.toml's witness must be an n at which the record beats its predecessor"
    else
      die s!"`decide +kernel` does not settle the witness comparison at {witness} within {budget} heartbeats and {fuelMemoryMb} MB: the record exceeds a limit, or does not reduce in the kernel (Lean's error above can be garbled when a limit stops it)"

/-- A wall-clock guard on the range probe, which runs up to `fuelRangeMax` comparisons in one process. -/
def rangeGuardMs : Nat := 1800000

/-- Gate 6, second part: `decide +kernel` must settle `0 ≤ record n` at every `n` from `nMin` to
`fuelRangeMax`, each within the problem's heartbeat budget. The statement is trivially true;
settling it makes the kernel evaluate `record n` to a numeral, so what is tested is that the
record is cheap to evaluate at every small `n`, not only at the witness, and a record that
searches for `f` is rejected. The predecessor is not evaluated: a slow predecessor does not
count against the new record. -/
def gateRange (probe : FilePath) (cfg : ProblemConfig) (module recordConst : String) : IO Unit := do
  let budget := cfg.fuelBudget
  let lo := cfg.nMin
  let hi := cfg.fuelRangeMax
  if hi < lo then
    note s!"fuel-range-max {hi} is below nMin {lo}; no range to check"
    return
  let cmp (n : Nat) := s!"0 ≤ {recordConst} {n}"
  -- line 1 is the import and line 2 a comment; each n then takes lines 3 + 2i and 4 + 2i
  let mut src := s!"import {module}\n-- The record evaluated at every n from {lo} to {hi}.\n"
  for n in [lo:hi + 1] do
    src := src ++ s!"set_option maxHeartbeats {budget} in\nexample : {cmp n} := by decide +kernel\n"
  IO.FS.writeFile probe src
  let pre := probe.toString ++ ":"
  let isError (l : String) := l.startsWith pre && (l.splitOn ": error").length > 1
  -- one failing n rejects the record, so Lean is stopped at the first error
  let (res, stopped, out) ← outputUntil
    { cmd := ← leanBin, args := #["-M", toString fuelMemoryMb, probe.toString] } rangeGuardMs isError
  match res, stopped with
  | some 0, false =>
    note s!"`decide +kernel` evaluates the record at every n from {lo} to {hi}, each within {budget} heartbeats"
  | none, false =>
    die s!"the range probe (n from {lo} to {hi}) did not finish within {rangeGuardMs / 1000}s"
  | _, _ =>
    -- the error names its line, and the line names the n
    let errors := (out.splitOn "\n").filter isError
    let failing := errors.filterMap fun l =>
      match ((l.dropS pre.length).splitOn ":").head? >>= String.toNat? with
      | some line => if line ≥ 3 then some (lo + (line - 3) / 2) else none
      | none => none
    match failing.min? with
    | some n =>
      IO.eprintln errors.head!
      die s!"`decide +kernel` does not settle {cmp n} within {budget} heartbeats, the default recursion depth and {fuelMemoryMb} MB: a record must be cheap to evaluate at every n from {lo} to {hi}, not only at the witness (problem.toml: fuel-range-max)"
    | none =>
      unless out.trimS.isEmpty do IO.print out
      die s!"the range probe (n from {lo} to {hi}) failed: the record exceeds {fuelMemoryMb} MB, or does not reduce in the kernel"

/-! ## The command -/

/-- Verify one directory; throws with the exit code on any outcome but ACCEPT. -/
unsafe def verifyDir (dir : String) (base : Option String) (accepted : Bool) : IO Unit := do
  let root ← root
  let loc ← match ← locate dir with | .ok l => pure l | .error e => die e
  let t := loc.t
  let k := loc.k
  let dir := loc.dir
  for f in [t.challenge k, t.comparatorJson k, t.problemToml] do
    unless ← f.pathExists do die s!"no Challenge {vtag k} for {t.problem}/{t.dir} (missing {f})"
  let metaPath := FilePath.mk dir / "metadata.toml"
  unless ← metaPath.pathExists do die s!"{dir} has no metadata.toml"
  let md ← Metadata.load metaPath
  if (md.name.getD "").trimS.isEmpty then die s!"{metaPath} has no `name` (the public credit)"
  unless md.basedOn.isEmpty do note s!"based on {", ".intercalate md.basedOn.toList} (metadata.toml; checked by the reviewer)"
  let cfg ← ProblemConfig.load t.problemToml
  unless cfg.directions.contains t.dir do die s!"{t.problem} has no {t.dir} track (problem.toml: {cfg.directions.toList})"
  -- rebase check: a version whose successor Challenge exists was already accepted
  unless accepted do
    if ← (t.challenge (k + 1)).pathExists then
      rebase s!"REBASE: {vtag k} of {t.problem} {t.dir} is already accepted ({t.challenge (k + 1)} exists).\n        Rename the directory to the open version and update the namespace and predecessor references (docs/CONTRIBUTING.md, Rebasing)."
  let module := moduleOfPath dir ++ ".Proof"
  unless loc.isFixture do
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (t.comparatorJson k)))
    unless (json.getObjValAs? String "solution_module").toOption == some module do
      fail s!"{t.comparatorJson k} names a different solution_module than {module}"

  -- gate 1: diff scope
  if let some base := base then
    IO.println s!"[1/6] diff path restriction against {base}"
    let out ← SqueezeBench.Tool.run { cmd := "git", args := #["diff", "--name-only", s!"{base}...HEAD", "--", ":/", s!":!{dir}"] }
    if out.exitCode != 0 then fail s!"git diff against {base} failed:\n{out.stderr.trimEndS}"
    let stray := out.stdout.trimS
    unless stray.isEmpty do die s!"the pull request touches files outside {dir}:\n{stray}"
    note s!"diff confined to {dir}"
  else
    IO.println "[1/6] diff path restriction SKIPPED (no --base); CI must always pass it"

  -- gate 2: how large the record is, and what Def.lean may contain
  IO.println "[2/6] size limits, and the Def.lean restriction (parsed, not elaborated)"
  unless ← (FilePath.mk dir / "Def.lean").pathExists do die s!"{dir} has no Def.lean"
  gateSize cfg (FilePath.mk dir)
  gateDef t k (FilePath.mk dir / "Def.lean")

  -- gate 3: Comparator
  IO.println "[3/6] Comparator"
  unless ← (FilePath.mk dir / "Proof.lean").pathExists do die s!"{dir} has no Proof.lean"
  checkHost
  let tools ← Tools.resolve root
  let ours ← checkToolchains
  checkManifestFresh root tools
  note s!"comparator {← shortSha "Comparator"} · lean4export {← shortSha "lean4export"} · toolchain {ours}"
  note s!"challenge {t.challengeModule k} · solution {module}"
  gateComparator root (t.comparatorJson k) tools module

  -- gate 4: the computation budget of the proofs
  IO.println "[4/6] computation budget (heartbeats per declaration and in all, no option overrides)"
  gateBudget root tools (FilePath.mk dir / "Proof.lean")

  -- gates 5-6: admissibility of the record, then the fuel budget
  let recordConst := t.recordName k
  let pid ← IO.Process.getPID
  let probe := root / s!"VerifyProbe_{pid}.lean"
  try
    IO.println "[5/6] admissibility (computability, no oracle reference)"
    gateAdmissible probe cfg module recordConst
    IO.println s!"[6/6] fuel budget (heartbeats and memory of `decide +kernel` at the witness, and at every n from {cfg.nMin} to {cfg.fuelRangeMax})"
    if k == 0 then note "a seed has no predecessor; skipping"
    else
      let some w := md.witness
        | die s!"{metaPath} declares no witness; set `witness` to the n₀ of your `strict` proof"
      gateFuel probe t cfg module (t.recordName (k - 1)) recordConst w
      gateRange probe cfg module recordConst
  finally
    if ← probe.pathExists then IO.FS.removeFile probe
  IO.println s!"ACCEPT: {dir}"

unsafe def run (args : List String) : IO UInt32 := do
  if args == ["-h"] || args == ["--help"] then IO.println usage; return 0
  let a ← match parseArgs args {} with | .ok a => pure a | .error e => fail e
  verifyDir a.dir a.base a.accepted
  return 0

end SqueezeBench.Tool.Verify
