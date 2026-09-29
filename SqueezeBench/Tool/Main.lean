import SqueezeBench.Tool.New
import SqueezeBench.Tool.Verify
import SqueezeBench.Tool.Audit
import SqueezeBench.Tool.Test
import SqueezeBench.Tool.Accept
import SqueezeBench.Tool.Bootstrap
import SqueezeBench.Tool.Budget

/-! Entry point of `lake exe squeeze`, the maintainer tool: dispatches to a subcommand and maps
its outcome to an exit code (0 success or ACCEPT, 1 rejection, 2 usage or infrastructure,
3 rebase needed). -/

open SqueezeBench.Tool

def usage : String := "\
usage: lake exe squeeze <subcommand> [args]

  new [Problem] [lower|upper] [options]        lay out the next record directory; asks for what is missing
  verify <record-dir> [--base <ref>] [--accepted]   run the admission gates on a record or fixture (Linux; after bootstrap)
  audit [Problem [lower|upper [V<k>]]]         verify every accepted record in scope
  test                                         verify every fixture and check its expected exit code
  budget-probe <Proof.lean>                    heartbeats of each command and in all (verify's gate 4)
  accept <Problem> <lower|upper> [--dry-run]   after a merge: open the next Challenge, update the README
  bootstrap                                    build the pinned verifier tools into .tools/

`lake exe squeeze <subcommand> --help` lists a subcommand's options."

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "new" :: rest => New.run rest
    | "verify" :: rest => Verify.run rest
    | "audit" :: rest => Audit.run rest
    | "test" :: rest => Test.run rest
    | "accept" :: rest => Accept.run rest
    | "bootstrap" :: rest => Bootstrap.run rest
    | "budget-probe" :: rest => Budget.run rest
    | [] | ["-h"] | ["--help"] => IO.println usage; pure 0
    | sub :: _ => infra s!"squeeze: unknown subcommand '{sub}' (try --help)"
  catch e =>
    (← IO.getStdout).flush
    match e with
    | .otherError code msg => IO.eprintln msg; pure code
    | .userError msg => IO.eprintln msg; pure 1
    | e => IO.eprintln s!"squeeze: {e}"; pure 2
