import SqueezeBench.Tool.Tree

/-! `squeeze bootstrap`: runs `scripts/bootstrap_tools.sh`, which stays a shell script because it
drives cargo, go, sha256sum and tar. -/

namespace SqueezeBench.Tool.Bootstrap

open SqueezeBench.Tool

def run (args : List String) : IO UInt32 := do
  let script := (← root) / "scripts" / "bootstrap_tools.sh"
  unless ← script.pathExists do infra s!"squeeze bootstrap: {script} is missing"
  runInherit { cmd := script.toString, args := args.toArray }

end SqueezeBench.Tool.Bootstrap
