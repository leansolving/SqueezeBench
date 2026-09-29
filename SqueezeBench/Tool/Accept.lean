import SqueezeBench.Tool.Toml
import SqueezeBench.Tool.Tree

/-! `squeeze accept`: after a record's pull request is merged, open the next version. Writes
`Challenges/<P>/<Dir>/V<k+1>.lean` and its Comparator config from a fixed template, and
appends the accepted version to the problem README's record row and *Record history*
table. It reads the record and writes nothing into it: what was verified is what stays. A
track whose seed `V000` has no Challenge yet gets that one too. -/

namespace SqueezeBench.Tool.Accept

open SqueezeBench.Tool
open System (FilePath)

def usage : String := "\
usage: lake exe squeeze accept <Problem> <lower|upper> [--dry-run]

Run after the pull request adding Records/<Dir>/V<k>/ was merged (and verified). Writes the
open Challenge Challenges/<Problem>/<Dir>/V<k+1>.{lean,comparator.json}, updates the README's
record row and history table, and validates by building the record and the new Challenge;
rolled back on failure, without git. A
seed V000 without a Challenge gets its V000 Challenge as well.
--dry-run prints what would be written and changes nothing."

/-- The tree is not in a state to accept (exit 1). -/
def die (msg : String) : IO α := reject s!"accept: {msg}"

/-- The tool itself could not do its job (exit 2). -/
def fail (msg : String) : IO α := infra s!"accept: {msg}"

/-! ## Templates (byte-identical to what the migration of 2026-09-11 wrote) -/

/-- The Challenge of a seed: `record` and `valid` only. -/
def seedChallenge (t : Track) : String :=
  let ns := t.ns 0
  s!"import SqueezeBench.Core
import SqueezeBench.Problems.{t.problem}.Def

/-!
# Challenge — {t.problem}, {t.dir} direction, V000

The trusted statement of the seed record. `record` is the definition hole
`Records/{t.dirCap}/V000/Def.lean` fills; `valid` is stated against `{t.fName}`, fully qualified
so that no `open` in the record can redirect it. A seed has no predecessor, so there is
nothing to improve on. Never edited.
-/

namespace {ns}

def record : SqueezeBench.BoundFn := sorry

theorem valid : {t.holdsName} {t.fName} record := sorry

end {ns}
"

/-- The Challenge of version `k ≥ 1`: beat `V<k-1>`. -/
def nextChallenge (t : Track) (k : Nat) : String :=
  let ns := t.ns k
  let prev := t.recordName (k - 1)
  s!"import SqueezeBench.Core
import {t.recordModule (k - 1)}.Def

/-!
# Challenge — {t.problem}, {t.dir} direction, {vtag k}

The trusted statement of record for version {vtag k}. `record` is the definition hole
`Records/{t.dirCap}/{vtag k}/Def.lean` fills; the three obligations are stated against `{t.fName}`,
`nMin` and the previous record `{prev}`, fully qualified so that no
`open` in the record can redirect them. Written once, when {vtag (k - 1)} was accepted; never edited.
-/

namespace {ns}

def record : SqueezeBench.BoundFn := sorry

theorem valid : {t.holdsName} {t.fName} record := sorry
theorem improves : {t.improvesName} {prev} record := sorry
theorem strict :
    {t.strictName} {t.nMinName} {prev} record := sorry

end {ns}
"

/-- The Comparator config of version `k`, laid out one entry per line. -/
def challengeJson (t : Track) (k : Nat) : String :=
  let ns := t.ns k
  let thms := if k == 0 then [s!"{ns}.valid"] else [s!"{ns}.valid", s!"{ns}.improves", s!"{ns}.strict"]
  let list (xs : List String) := "[\n" ++ ",\n".intercalate (xs.map fun x => s!"    \"{x}\"") ++ "\n  ]"
  s!"\{
  \"challenge_module\": \"{t.challengeModule k}\",
  \"solution_module\": \"{t.recordModule k}.Proof\",
  \"theorem_names\": {list thms},
  \"definition_names\": {list [s!"{ns}.record"]},
  \"permitted_axioms\": {list ["propext", "Quot.sound", "Classical.choice"]},
  \"enable_nanoda\": true
}
"

/-! ## README -/

/-- Append one row to the README's *Record history* table, creating section and table as needed. -/
def appendHistory (readme : FilePath) (dirCap version date author witness old new : String) : IO Unit := do
  let mut lines := ((← IO.FS.readFile readme).dropEndWhileS (· == '\n')).splitOn "\n" |>.toArray
  let row := s!"| {version} | {date} | {author} | {witness} | {old} → {new} |"
  let hdr := "## Record history"
  unless lines.contains hdr do
    lines := lines ++ #["", hdr, "", "One row per accepted version, oldest first, appended by `lake exe squeeze accept`.",
      "The author is the `name` in the record's `metadata.toml`."]
  let sub := s!"### {dirCap}"
  let h := (lines.findIdx? (· == hdr)).getD 0
  let mut «end» := lines.size
  for j in [h + 1 : lines.size] do
    if lines[j]!.startsWith "## " then «end» := j; break
  unless (lines.extract h «end»).contains sub do
    lines := lines.extract 0 «end» ++ #["", sub, "", "| version | date | author | witness | value at the witness |",
      "|---|---|---|---|---|"] ++ lines.extract «end» lines.size
    «end» := «end» + 5
  let s := ((lines.extract h «end»).findIdx? (· == sub)).getD 0 + h
  let mut last := s
  for j in [s + 1 : «end»] do
    if lines[j]!.startsWith "|" then last := j
    else if lines[j]!.startsWith "### " then break
  lines := lines.insertIdx! (last + 1) row
  IO.FS.writeFile readme ("\n".intercalate lines.toList ++ "\n")
  note s!"{readme}: {sub} += {row}"

/-- The README's `| <Dir> record | … |` row for version `k`. -/
def recordRow (t : Track) (k : Nat) (author date : String) (witness : Option Nat) : String :=
  let tail := match witness with
    | some w => s!"beats {vtag (k - 1)} at witness `{w}` ({author}, {date})"
    | none => s!"({author}, {date})"
  s!"| {t.dirCap} record | `Records/{t.dirCap}/{vtag k}/` — {tail} |"

/-- Replace the README's record row for this direction; absent rows are reported, not created. -/
def updateRecordRow (readme : FilePath) (t : Track) (row : String) : IO Unit := do
  let text ← IO.FS.readFile readme
  let key := s!"| {t.dirCap} record | "
  let lines := text.splitOn "\n"
  if lines.any (·.startsWith key) then
    IO.FS.writeFile readme ("\n".intercalate (lines.map fun l => if l.startsWith key then row else l))
    note s!"README: '{key.trimS}' row updated"
  else
    note s!"README has no '{key.trimS}' row; add one by hand"

/-! ## The command -/

structure Plan where
  t : Track
  k : Nat
  author : String
  witness : Option Nat
  date : String
  writeSeed : Bool

/-- Commit date of the record directory, else today. -/
def recordDate (dir : FilePath) : IO String := do
  let out ← run { cmd := "git", args := #["log", "-1", "--format=%cs", "--", dir.toString] }
  let d := out.stdout.trimS
  if out.exitCode == 0 && !d.isEmpty then pure d else utcToday

def plan (problem dir : String) (dryRun : Bool) : IO Plan := do
  let t ← match Track.ofDirection problem dir with | .ok t => pure t | .error e => die e
  unless ← t.problemToml.pathExists do die s!"no problem '{problem}' (missing {t.problemToml})"
  let cfg ← ProblemConfig.load t.problemToml
  unless cfg.directions.contains t.dir do die s!"{problem} has no {dir} track (problem.toml: {cfg.directions.toList})"
  let some k ← t.currentVersion | die s!"{t.recordsDir} holds no record; seed V000 first (docs/ADDING_A_PROBLEM.md)"
  let rdir := t.recordDir k
  for f in ["Def.lean", "Proof.lean", "metadata.toml"] do
    unless ← (rdir / f).pathExists do die s!"{rdir} has no {f}"
  let md ← Metadata.load (rdir / "metadata.toml")
  let some author := md.name | die s!"{rdir}/metadata.toml has no `name` (the public credit)"
  if author.trimS.isEmpty then die s!"{rdir}/metadata.toml has no `name` (the public credit)"
  let writeSeed := k == 0 && !(← (t.challenge 0).pathExists)
  if k > 0 then
    unless ← (t.challenge k).pathExists do
      die s!"{t.challenge k} is missing: {vtag k} was never opened, so it cannot have been verified"
  if ← (t.challenge (k + 1)).pathExists then
    die s!"{t.challenge (k + 1)} exists: {vtag k} is already accepted"
  let date ← recordDate rdir
  note s!"{problem} {dir}: {vtag k} accepted ({author}, {date}) → opening {vtag (k + 1)}"
  let author := if md.basedOn.isEmpty then author
    else s!"{author}; based on {", ".intercalate md.basedOn.toList}"
  pure { t, k, author, witness := md.witness, date, writeSeed }

/-- The value of the previous and the new record at the witness, by `#eval` on accepted code. -/
def valuesAtWitness (root : FilePath) (p : Plan) (w : Nat) : IO (String × String) := do
  let t := p.t
  let build ← run { cmd := "lake", args := #["build", s!"{t.recordModule p.k}.Def"] }
  if build.exitCode != 0 then die s!"lake build {t.recordModule p.k}.Def failed:\n{build.stderr.trimEndS}"
  let probe := root / s!"AcceptProbe_{← IO.Process.getPID}.lean"
  try
    IO.FS.writeFile probe s!"import {t.recordModule p.k}.Def
#eval {t.recordName (p.k - 1)} {w}
#eval {t.recordName p.k} {w}
"
    let out ← run { cmd := ← leanBin, args := #[probe.toString] }
    if out.exitCode != 0 then die s!"could not evaluate the records at the witness:\n{out.stdout}{out.stderr}"
    match (out.stdout.splitOn "\n").filter (!·.trimS.isEmpty) |>.map String.trimS with
    | [vold, vnew] => pure (vold, vnew)
    | _ => die s!"unexpected probe output:\n{out.stdout}"
  finally
    if ← probe.pathExists then IO.FS.removeFile probe

/-- Accept for real, rolling the tree back if anything fails. -/
def apply (root : FilePath) (p : Plan) : IO Unit := do
  let t := p.t
  let written : Array FilePath :=
    (if p.writeSeed then #[t.challenge 0, t.comparatorJson 0] else #[]) ++ #[t.challenge (p.k + 1), t.comparatorJson (p.k + 1)]
  -- the rollback restores this copy, so it does not depend on the state of the git index
  let readmeBefore ← IO.FS.readFile t.readme
  try
    IO.FS.createDirAll t.challengeDir
    if p.writeSeed then
      IO.FS.writeFile (t.challenge 0) (seedChallenge t)
      IO.FS.writeFile (t.comparatorJson 0) (challengeJson t 0)
      note s!"{t.challenge 0} written (seed)"
    IO.FS.writeFile (t.challenge (p.k + 1)) (nextChallenge t (p.k + 1))
    IO.FS.writeFile (t.comparatorJson (p.k + 1)) (challengeJson t (p.k + 1))
    note s!"{t.challenge (p.k + 1)} written"
    updateRecordRow t.readme t (recordRow t p.k p.author p.date p.witness)
    if p.k > 0 then
      let (vold, vnew) ← match p.witness with
        | some w => valuesAtWitness root p w
        | none => pure ("—", "—")
      appendHistory t.readme t.dirCap (vtag p.k) p.date p.author
        (match p.witness with | some w => toString w | none => "—") vold vnew
    -- only the accepted record and the Challenges written; other records in the tree may be work in progress
    let targets := #[s!"{t.recordModule p.k}.Proof", t.challengeModule (p.k + 1)]
      ++ (if p.writeSeed then #[t.challengeModule 0] else #[])
    let build ← run { cmd := "lake", args := #["build"] ++ targets }
    if build.exitCode != 0 then
      let errs := (build.stdout ++ build.stderr).splitOn "\n" |>.filter (·.startsWith "error") |>.take 5
      for e in errs do IO.eprintln e
      die "lake build failed after accepting"
  catch e =>
    IO.eprintln "accept: failed — rolling back"
    for f in written do
      if ← f.pathExists then IO.FS.removeFile f
    IO.FS.writeFile t.readme readmeBefore
    throw e

def run (args : List String) : IO UInt32 := do
  if args == ["-h"] || args == ["--help"] then IO.println usage; return 0
  let (problem, dir, dryRun) ← match args with
    | [p, d] => pure (p, d, false)
    | [p, d, "--dry-run"] | ["--dry-run", p, d] => pure (p, d, true)
    | _ => fail usage
  let root ← root
  let p ← plan problem dir dryRun
  if dryRun then
    if p.writeSeed then
      IO.println s!"===== {p.t.challenge 0}"; IO.print (seedChallenge p.t)
      IO.println s!"===== {p.t.comparatorJson 0}"; IO.print (challengeJson p.t 0)
    IO.println s!"===== {p.t.challenge (p.k + 1)}"; IO.print (nextChallenge p.t (p.k + 1))
    IO.println s!"===== {p.t.comparatorJson (p.k + 1)}"; IO.print (challengeJson p.t (p.k + 1))
    IO.println s!"===== {p.t.readme} record row"
    IO.println (recordRow p.t p.k p.author p.date p.witness)
    IO.println "===== dry run: nothing written"
    return 0
  apply root p
  IO.println s!"ACCEPTED: {problem} {dir} {vtag p.k}; {vtag (p.k + 1)} is open  (review the README, then commit)"
  return 0

end SqueezeBench.Tool.Accept
