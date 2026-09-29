import Lean

/-! Process helpers for the `squeeze` tool: every external program is spawned with an argv array,
never through a shell, and failures carry the exit code `squeeze` should end with. -/

/-! `String` operations that return a `String` rather than a `String.Slice`. -/
namespace String
def trimS (s : String) : String := s.trimAscii.toString
def trimEndS (s : String) : String := s.trimAsciiEnd.toString
def takeWhileS (s : String) (p : Char → Bool) : String := (s.takeWhile p).toString
def dropWhileS (s : String) (p : Char → Bool) : String := (s.dropWhile p).toString
def dropEndWhileS (s : String) (p : Char → Bool) : String := (s.dropEndWhile p).toString
def dropS (s : String) (n : Nat) : String := (s.drop n).toString
def takeS (s : String) (n : Nat) : String := (s.take n).toString
def dropEndS (s : String) (n : Nat) : String := (s.dropEnd n).toString
end String

namespace SqueezeBench.Tool

/-- Exit codes: 0 success or ACCEPT, 1 a judged rejection, 2 usage or infrastructure, 3 rebase. -/
def exitWith (code : UInt32) (msg : String) : IO α := throw (.otherError code msg)

def reject (msg : String) : IO α := exitWith 1 msg
def infra (msg : String) : IO α := exitWith 2 msg
def rebase (msg : String) : IO α := exitWith 3 msg

/-- An indented progress line. -/
def note (msg : String) : IO Unit := do
  IO.println s!"  {msg}"
  (← IO.getStdout).flush

/-- A command line to spawn; `env` entries override or (with `none`) unset variables. -/
structure Cmd where
  cmd : String
  args : Array String := #[]
  cwd : Option System.FilePath := none
  env : Array (String × Option String) := #[]

def Cmd.render (c : Cmd) : String := " ".intercalate (c.cmd :: c.args.toList)

private def Cmd.spawnArgs (c : Cmd) : IO.Process.SpawnArgs :=
  { cmd := c.cmd, args := c.args, cwd := c.cwd, env := c.env }

/-- Run to completion with captured output; a spawn failure (e.g. missing binary) is an exit-2 error. -/
def run (c : Cmd) : IO IO.Process.Output := do
  try IO.Process.output c.spawnArgs
  catch e => infra s!"squeeze: cannot run `{c.render}`: {e}"

/-- Captured stdout of a command that must succeed; its stderr is reported on failure. -/
def runOk (c : Cmd) : IO String := do
  let out ← run c
  if out.exitCode != 0 then
    infra s!"squeeze: `{c.render}` failed (exit {out.exitCode}):\n{out.stderr.trimEndS}"
  pure out.stdout

/-- Run with inherited stdio (the child's output streams to the terminal); returns the exit code. -/
def runInherit (c : Cmd) : IO UInt32 := do
  let child ← try IO.Process.spawn c.spawnArgs
    catch e => infra s!"squeeze: cannot run `{c.render}`: {e}"
  child.wait

/-- Captured stdout and stderr, with the child killed after `ms` milliseconds (exit code `none`). -/
def outputWithTimeout (c : Cmd) (ms : Nat) : IO (Option UInt32 × String) := do
  let child ← try IO.Process.spawn { c.spawnArgs with stdout := .piped, stderr := .piped }
    catch e => infra s!"squeeze: cannot run `{c.render}`: {e}"
  -- drain both pipes while waiting, so a chatty child cannot block on a full pipe
  let out ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
  let err ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
  let deadline := (← IO.monoMsNow) + ms
  let mut code : Option UInt32 := none
  repeat
    if let some c ← child.tryWait then
      code := some c
      break
    if (← IO.monoMsNow) > deadline then
      child.kill
      let _ ← child.wait
      break
    IO.sleep 50
  let text (t : Task (Except IO.Error String)) : String := match t.get with | .ok s => s | .error _ => ""
  pure (code, text out ++ text err)

/-- Like `outputWithTimeout`, but the child is also killed as soon as a line of its stdout
satisfies `stop`. Returns the exit code (`none` when killed), whether `stop` matched, and the output. -/
def outputUntil (c : Cmd) (ms : Nat) (stop : String → Bool) : IO (Option UInt32 × Bool × String) := do
  let child ← try IO.Process.spawn { c.spawnArgs with stdout := .piped, stderr := .piped }
    catch e => infra s!"squeeze: cannot run `{c.render}`: {e}"
  let hit ← IO.mkRef false
  let buf ← IO.mkRef ""
  -- read stdout line by line, so a matching line is seen while the child still runs
  let out ← IO.asTask (prio := .dedicated) do
    repeat
      let l ← child.stdout.getLine
      if l.isEmpty then break
      buf.modify (· ++ l)
      if stop l then hit.set true
  let err ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
  let deadline := (← IO.monoMsNow) + ms
  let mut code : Option UInt32 := none
  repeat
    if ← hit.get then
      child.kill
      let _ ← child.wait
      break
    if let some c ← child.tryWait then
      code := some c
      break
    if (← IO.monoMsNow) > deadline then
      child.kill
      let _ ← child.wait
      break
    IO.sleep 50
  let _ := out.get
  let errText := match err.get with | .ok s => s | .error _ => ""
  pure (code, ← hit.get, (← buf.get) ++ errText)

/-- Wall-clock milliseconds taken by an action. -/
def timedMs (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  pure (a, (← IO.monoMsNow) - t0)

/-- Whether the effective user is root (`id -u`), which the sandbox forbids. -/
def isRoot : IO Bool := do
  pure ((← runOk { cmd := "id", args := #["-u"] }).trimS == "0")

/-- First directory on `PATH` holding `name`, if any. -/
def findOnPath (name : String) : IO (Option System.FilePath) := do
  let some path ← IO.getEnv "PATH" | return none
  for dir in path.splitOn ":" do
    if dir.isEmpty then continue
    let p := System.FilePath.mk dir / name
    if ← p.pathExists then return some p
  return none

/-- The absolute `lean` binary Lake exported, else whatever `lean` is on `PATH`. -/
def leanBin : IO String := do
  pure ((← IO.getEnv "LEAN").getD "lean")

end SqueezeBench.Tool
