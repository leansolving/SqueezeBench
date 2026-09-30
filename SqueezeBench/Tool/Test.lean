import SqueezeBench.Tool.Toml
import SqueezeBench.Tool.Tree

/-! `squeeze test`: run `squeeze verify` on every fixture under `Fixtures/<P>/<Name>/` and compare the
exit code with the `expect` field of its `metadata.toml`. The fixtures are the regression
tests of the gates: one per gate, two whose proofs rest on native evaluation, one that must
be accepted, and one that must be turned away for rebase.

A fixture is judged against the Challenge of the version it names, which stays in the tree, so
`verify` runs with `--accepted` (no rebase check) and accepting a new record does not break the
fixtures. Only a fixture that expects the rebase exit code keeps the check. -/

namespace SqueezeBench.Tool.Test

open SqueezeBench.Tool
open System (FilePath)

def usage : String := "\
usage: lake exe squeeze test

Runs `lake exe squeeze verify` on each Fixtures/<Problem>/<Name>/ directory and checks the exit
code against `expect` in its metadata.toml. The rebase check runs only for a fixture that
expects exit code 3. Exit 0 when every fixture behaves, 1 otherwise."

def fail (msg : String) : IO α := infra s!"squeeze test: {msg}"

/-- Every fixture directory, sorted. -/
def fixtures : IO (Array String) := do
  let mut out := #[]
  let top := FilePath.mk "Fixtures"
  unless ← top.isDir do fail "no Fixtures/ directory"
  for p in ← top.readDir do
    unless ← p.path.isDir do continue
    for f in ← p.path.readDir do
      if ← (f.path / "metadata.toml").pathExists then out := out.push f.path.toString
  pure (out.qsort (· < ·))

def run (args : List String) : IO UInt32 := do
  if args == ["-h"] || args == ["--help"] then IO.println usage; return 0
  unless args.isEmpty do fail usage
  let _ ← root
  let dirs ← fixtures
  if dirs.isEmpty then fail "no fixtures found"
  let squeeze ← IO.appPath
  let mut results : Array (String × Nat × UInt32) := #[]
  for d in dirs do
    let md ← Metadata.load (FilePath.mk d / "metadata.toml")
    let some expect := md.expect | fail s!"{d}/metadata.toml has no `expect` (the exit code verify must produce)"
    IO.println s!"===== {d}  (expect {expect})"
    let args := if expect == 3 then #["verify", d] else #["verify", d, "--accepted"]
    let code ← runInherit { cmd := squeeze.toString, args }
    results := results.push (d, expect, code)
  IO.println "===== test summary"
  let mut failed := false
  for (d, expect, code) in results do
    let ok := code.toNat == expect
    IO.println s!"  {if ok then "PASS" else "FAIL"}  {d}  expected {expect}, got {code}"
    if !ok then failed := true
  return (if failed then 1 else 0)

end SqueezeBench.Tool.Test
