import Lean.Data.Json
import Std.Time
import SqueezeBench.Tool.Proc

/-! Where things live in this repository, for the `squeeze` tool: the paths and names of one
version of one track (a problem in one direction), the current and open versions, and the
pins the tree carries. Every path is version-indexed: a record is `Records/<Dir>/V<k>/`, its
Challenge is `Challenges/<P>/<Dir>/V<k>.lean`, and both declare `record`, `valid`,
`improves`, `strict` in the namespace `SqueezeBench.<P>.<Dir>.V<k>`. -/

namespace SqueezeBench.Tool

open System (FilePath)

/-- The package root: `lake exe squeeze` runs there, with Lake's `LEAN_PATH` exported. -/
def root : IO FilePath := do
  let cwd ← IO.currentDir
  unless (← (cwd / "lakefile.toml").pathExists) && (← IO.getEnv "LEAN_PATH").isSome do
    infra "squeeze: run from the package root as `lake exe squeeze …`"
  pure cwd

def pad3 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (3 - min 3 s.length) ++ s

/-- `V007` for `7`. -/
def vtag (k : Nat) : String := "V" ++ pad3 k

/-- The `k` of a `V<k>` name (three or more digits), if it has that shape. -/
def parseVtag (s : String) : Option Nat :=
  if s.startsWith "V" && s.length ≥ 4 && (s.dropS 1).all Char.isDigit then some (s.dropS 1).toNat!
  else none

/-- Today's date, `YYYY-MM-DD`, in UTC. -/
def utcToday : IO String := do
  let ts ← Std.Time.Timestamp.now
  let dt : Std.Time.DateTime .UTC := Std.Time.DateTime.ofTimestamp ts .UTC
  pure (dt.format "uuuu-MM-dd")

/-- A path argument with a leading `./` and a trailing `/` removed. -/
def normalizeDir (p : String) : String :=
  let p := if p.startsWith "./" then p.dropS 2 else p
  if p.endsWith "/" then p.dropEndS 1 else p

/-- `Fixtures/Tutorial/Bob` → `Fixtures.Tutorial.Bob`. -/
def moduleOfPath (p : String) : String :=
  ".".intercalate ((normalizeDir p).splitOn "/")

/-- One problem in one direction (`lower` or `upper`): the paths and names every subcommand needs. -/
structure Track where
  problem : String
  dir : String
  deriving Repr, BEq

namespace Track

def ofDirection (problem dir : String) : Except String Track :=
  if dir == "lower" || dir == "upper" then .ok { problem, dir }
  else .error s!"direction must be lower or upper, not '{dir}'"

def dirCap (t : Track) : String := t.dir.capitalize
def isLower (t : Track) : Bool := t.dir == "lower"
def problemToml (t : Track) : FilePath := "Challenges" / t.problem / "problem.toml"
def challengeDir (t : Track) : FilePath := "Challenges" / t.problem / t.dirCap
def challenge (t : Track) (k : Nat) : FilePath := t.challengeDir / s!"{vtag k}.lean"
def comparatorJson (t : Track) (k : Nat) : FilePath := t.challengeDir / s!"{vtag k}.comparator.json"
def challengeModule (t : Track) (k : Nat) : String := s!"Challenges.{t.problem}.{t.dirCap}.{vtag k}"
def problemDir (t : Track) : FilePath := "SqueezeBench" / "Problems" / t.problem
def readme (t : Track) : FilePath := t.problemDir / "README.md"
def recordsDir (t : Track) : FilePath := t.problemDir / "Records" / t.dirCap
def recordDir (t : Track) (k : Nat) : FilePath := t.recordsDir / vtag k
/-- `SqueezeBench.Problems.<P>.Records.<Dir>.V<k>`; append `.Def` or `.Proof`. -/
def recordModule (t : Track) (k : Nat) : String :=
  s!"SqueezeBench.Problems.{t.problem}.Records.{t.dirCap}.{vtag k}"
def ns (t : Track) (k : Nat) : String := s!"SqueezeBench.{t.problem}.{t.dirCap}.{vtag k}"
def recordName (t : Track) (k : Nat) : String := t.ns k ++ ".record"
def validName (t : Track) (k : Nat) : String := t.ns k ++ ".valid"
def fName (t : Track) : String := s!"SqueezeBench.{t.problem}.f"
def nMinName (t : Track) : String := s!"SqueezeBench.{t.problem}.nMin"
def holdsName (t : Track) : String := if t.isLower then "SqueezeBench.LowerBoundHolds" else "SqueezeBench.UpperBoundHolds"
def improvesName (t : Track) : String := if t.isLower then "SqueezeBench.ImprovesLower" else "SqueezeBench.ImprovesUpper"
def strictName (t : Track) : String :=
  if t.isLower then "SqueezeBench.StrictlyImprovesLower" else "SqueezeBench.StrictlyImprovesUpper"

end Track

/-- The `V<k>` entries of a directory (optionally with a suffix such as `.lean`), sorted. -/
def versionsIn (dir : FilePath) (suffix : String := "") : IO (Array Nat) := do
  unless ← dir.isDir do return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if e.fileName.endsWith suffix then
      if let some k := parseVtag (e.fileName.dropEndS suffix.length) then out := out.push k
  pure (out.qsort (· < ·))

/-- The accepted versions of a track, `Records/<Dir>/V*`. -/
def Track.versions (t : Track) : IO (Array Nat) := versionsIn t.recordsDir

/-- The highest record version in the tree: the standing record. -/
def Track.currentVersion (t : Track) : IO (Option Nat) := do pure (← t.versions).back?

/-- The highest Challenge version: the one a new submission answers. -/
def Track.openVersion (t : Track) : IO (Option Nat) := do
  pure (← versionsIn t.challengeDir ".lean").back?

/-- A record or fixture directory, resolved to its track and version. -/
structure Located where
  t : Track
  k : Nat
  dir : String
  isFixture : Bool

/-- `SqueezeBench.<P>.<Dir>.V<k>` split into its parts, if a namespace has that shape. -/
def parseNs (s : String) : Option (String × String × Nat) :=
  match s.splitOn "." with
  | ["SqueezeBench", p, d, v] =>
    if d == "Lower" || d == "Upper" then (parseVtag v).map fun k => (p, d.toLower, k) else none
  | _ => none

/-- Resolve a directory from the `namespace` line of its `Def.lean`, cross-checked against the
path: `SqueezeBench/Problems/<P>/Records/<Dir>/V<k>` or `Fixtures/<P>/<Name>`. -/
def locate (dir : String) : IO (Except String Located) := do
  let dir := normalizeDir dir
  let defFile := FilePath.mk dir / "Def.lean"
  unless ← defFile.pathExists do return .error s!"{dir} has no Def.lean"
  let text ← IO.FS.readFile defFile
  let nsLine := (text.splitOn "\n").find? (·.startsWith "namespace ")
  let some (p, d, k) := nsLine.bind fun l => parseNs (l.dropS "namespace ".length).trimS
    | return .error s!"{defFile}: expected a line `namespace SqueezeBench.<Problem>.<Lower|Upper>.V<k>`"
  let t : Track := { problem := p, dir := d }
  match dir.splitOn "/" with
  | ["SqueezeBench", "Problems", p', "Records", d', v'] =>
    unless p' == p && d' == t.dirCap && v' == vtag k do
      return .error s!"{dir}: the path says {p'}/{d'}/{v'} but Def.lean opens namespace {t.ns k}"
    pure (.ok { t, k, dir, isFixture := false })
  | ["Fixtures", p', _] =>
    unless p' == p do return .error s!"{dir}: the path says {p'} but Def.lean opens namespace {t.ns k}"
    pure (.ok { t, k, dir, isFixture := true })
  | _ => pure (.error s!"{dir} is neither SqueezeBench/Problems/<P>/Records/<Dir>/V<k> nor Fixtures/<P>/<Name>")

/-- The problems that have a Challenge directory, sorted. -/
def problems : IO (Array String) := do
  let mut out := #[]
  for e in ← FilePath.readDir "Challenges" do
    if ← e.path.isDir then out := out.push e.fileName
  pure (out.qsort (· < ·))

/-- `4.31.0` from `lean-toolchain`'s `leanprover/lean4:v4.31.0`. -/
def leanToolchainVersion : IO String := do
  let s := (← IO.FS.readFile "lean-toolchain").trimS
  let prefix_ := "leanprover/lean4:v"
  let v := if s.startsWith prefix_ then s.dropS prefix_.length else s
  if v.isEmpty then infra "squeeze: cannot read lean-toolchain"
  pure v

/-- The pinned revision of a package in `lake-manifest.json`. -/
def manifestRev (pkg : String) : IO String := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let pkgs ← IO.ofExcept (j.getObjVal? "packages" >>= (·.getArr?))
  for p in pkgs do
    if (p.getObjValAs? String "name").toOption == some pkg then
      if let .ok rev := p.getObjValAs? String "rev" then return rev
  infra s!"squeeze: lake-manifest.json has no package {pkg}"

end SqueezeBench.Tool
