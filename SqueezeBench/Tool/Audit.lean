import SqueezeBench.Tool.Toml
import SqueezeBench.Tool.Tree

/-! `squeeze audit`: `squeeze verify --accepted` on every accepted record directory in scope. Each
directory is verified in a child process, because loading a Lean environment is not safely
repeatable inside one process. -/

namespace SqueezeBench.Tool.Audit

open SqueezeBench.Tool
open System (FilePath)

def usage : String := "\
usage: lake exe squeeze audit [Problem [lower|upper [V<k>]]]

Runs `lake exe squeeze verify <dir> --accepted` on every accepted record in scope (all problems by
default) and prints a summary. Exit 0 when every record passes, 1 when any is rejected, 2 when
the tools fail. Comparator's second trust assumption holds only from a fresh checkout with a
clean build directory; a local run re-checks records that are already built."

def fail (msg : String) : IO α := infra s!"squeeze audit: {msg}"

/-- The record directories to audit, in order. -/
def scope (problem : Option String) (dir : Option String) (version : Option Nat) : IO (Array String) := do
  let ps ← match problem with
    | some p =>
      unless (← problems).contains p do fail s!"no problem '{p}'"
      pure #[p]
    | none => problems
  let mut out := #[]
  for p in ps do
    let cfg ← ProblemConfig.load (FilePath.mk "Challenges" / p / "problem.toml")
    for d in cfg.directions do
      if let some d' := dir then if d' != d then continue
      let t : Track := { problem := p, dir := d }
      let ks ← match version with
        | some k => pure #[k]
        | none => t.versions
      for k in ks do
        unless ← (t.recordDir k).isDir do fail s!"{t.recordDir k} does not exist"
        out := out.push (t.recordDir k).toString
  pure out

def run (args : List String) : IO UInt32 := do
  if args == ["-h"] || args == ["--help"] then IO.println usage; return 0
  let _ ← root
  let (problem, dir, version) ← match args with
    | [] => pure (none, none, none)
    | [p] => pure (some p, none, none)
    | [p, d] => pure (some p, some d, none)
    | [p, d, v] => match parseVtag v with
      | some k => pure (some p, some d, some k)
      | none => fail s!"'{v}' is not a version (V<k>)"
    | _ => fail usage
  if let some d := dir then
    if let .error e := Track.ofDirection "" d then fail e
  let dirs ← scope problem dir version
  if dirs.isEmpty then fail "nothing to audit"
  let squeeze ← IO.appPath
  let mut results : Array (String × UInt32) := #[]
  for d in dirs do
    IO.println s!"===== {d}"
    let code ← runInherit { cmd := squeeze.toString, args := #["verify", d, "--accepted"] }
    results := results.push (d, code)
  IO.println "===== audit summary"
  let mut worst : UInt32 := 0
  for (d, code) in results do
    let verdict := match code with
      | 0 => "ACCEPT" | 1 => "REJECT" | 3 => "REBASE" | _ => "ERROR"
    IO.println s!"  {verdict}  {d}"
    if code == 2 then worst := 2
    else if code != 0 && worst != 2 then worst := 1
  return worst

end SqueezeBench.Tool.Audit
