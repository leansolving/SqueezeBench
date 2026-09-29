import SqueezeBench.Tool.Toml
import SqueezeBench.Tool.Tree

/-! `squeeze new`: lay out the next record directory so that only the mathematics is left to
write. The four holes are copied from the open Challenge with their `sorry` bodies rewritten,
`record` into `Def.lean` and the three theorems into `Proof.lean`; `metadata.toml` carries the
credit and the witness, and `REPORT.md` is a template for how the record was obtained. Anything
not given on the command line is asked for on the terminal, or is an error when there is no
terminal. -/

namespace SqueezeBench.Tool.New

open SqueezeBench.Tool
open System (FilePath)

def usage : String := "\
usage: lake exe squeeze new [Problem] [lower|upper] [options]

  --name \"Full Name\"    public credit (default: git config user.name)
  --idiom patch|fold    pre-fill `record` and the mechanical obligations (CONTRIBUTING idioms 1, 2)
  --at <n0>             the witness: the n at which the new record beats the previous one
                        (required with --idiom patch)
  --value <y0>          the new value at n0 (patch only)

Writes SqueezeBench/Problems/<Problem>/Records/<Dir>/V<k>/{Def.lean,Proof.lean,metadata.toml,REPORT.md}
for the open version V<k>. Missing values are asked for on the terminal; with no arguments at
all every choice is asked."

structure Opts where
  problem : Option String := none
  direction : Option String := none
  name : Option String := none
  idiom : Option String := none
  at? : Option String := none
  value? : Option String := none
  help : Bool := false

private def flags : List String := ["--name", "--idiom", "--at", "--value"]

def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "-h" :: _, o | "--help" :: _, o => .ok { o with help := true }
  | f :: v :: rest, o =>
    if flags.contains f && !v.startsWith "--" then
      match f with
      | "--name" => parseArgs rest { o with name := v }
      | "--idiom" => parseArgs rest { o with idiom := v }
      | "--at" => parseArgs rest { o with at? := v }
      | _ => parseArgs rest { o with value? := v }
    else positional f (v :: rest) o
  | a :: rest, o => positional a rest o
where
  positional (a : String) (rest : List String) (o : Opts) : Except String Opts :=
    if flags.contains a then .error s!"{a} needs a value"
    else if a.startsWith "-" then .error s!"unknown option {a} (try --help)"
    else if o.problem.isNone then parseArgs rest { o with problem := a }
    else if o.direction.isNone then parseArgs rest { o with direction := a }
    else .error s!"unexpected argument '{a}' (try --help)"

/-! ## Validation, shared by the flag and the prompt paths -/

def validateProblem (known : Array String) (p : String) : Except String String :=
  if known.contains p then .ok p
  else .error s!"no problem '{p}'; available: {" ".intercalate known.toList}"

def validateDirection (cfg : ProblemConfig) (d : String) : Except String String := do
  let t ← Track.ofDirection cfg.problem d
  if cfg.directions.contains d then pure t.dir
  else throw s!"{cfg.problem} has no {d} track (problem.toml: {cfg.directions.toList})"

def validateNat (what : String) (s : String) : Except String String :=
  if !s.isEmpty && s.all Char.isDigit then .ok s else .error s!"{what} must be a natural number"

def validateNonEmpty (what : String) (s : String) : Except String String :=
  if s.trimS.isEmpty then .error s!"{what} must not be empty" else .ok s.trimS

def validateIdiom (s : String) : Except String String :=
  if s == "patch" || s == "fold" || s == "none" then .ok s
  else .error s!"--idiom must be patch or fold, not '{s}'"

/-! ## Terminal prompts -/

def die (msg : String) : IO α := infra s!"squeeze new: {msg}"

/-- Ask until `validate` accepts; Enter takes `default` when there is one. -/
partial def ask (label : String) (default : Option String)
    (validate : String → Except String String) : IO String := do
  let stdout ← IO.getStdout
  stdout.putStr (match default with | some d => s!"{label} [{d}]: " | none => s!"{label}: ")
  stdout.flush
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then die "end of input"
  let ans := line.trimS
  let ans := if ans.isEmpty then default.getD "" else ans
  match validate ans with
  | .ok v => pure v
  | .error e => IO.eprintln s!"  {e}"; ask label default validate

/-- A value from the command line, else its default, else a prompt, else an error; in
guided mode (no arguments at all) a default is offered on the prompt rather than taken. -/
def resolve (given default : Option String) (label missing : String)
    (validate : String → Except String String) (tty guided : Bool) : IO String := do
  match given with
  | some v => match validate v with | .ok v => pure v | .error e => die e
  | none =>
    if let some d := default then
      if !(guided && tty) then return d
    if tty then ask label default validate
    else match default with
      | some d => pure d
      | none => die missing

/-- `git config <key>`, if set. -/
def gitConfig (key : String) : IO (Option String) := do
  let out ← run { cmd := "git", args := #["config", key] }
  let v := out.stdout.trimS
  pure (if out.exitCode == 0 && !v.isEmpty then some v else none)

/-! ## The skeleton -/

/-- The text replacing ` sorry` after each hole's `:=`, and the helper blocks that go before
`record` in `Def.lean` and before `valid` in `Proof.lean`. -/
def holeBodies (t : Track) (k : Nat) (idiom : Option String) (at? value? : Option Nat) :
    List (String × String) × String × String :=
  let cur := t.recordName (k - 1)
  let curValid := t.validName (k - 1)
  let f := t.fName
  let nmin := t.nMinName
  let lower := t.isLower
  let prime := if lower then "" else "'"
  let fold := if lower then "maxWith" else "minWith"
  match idiom with
  | some "patch" =>
    let n0 := at?.getD 0
    let y0 := value?.getD 0
    let math := if lower then s!"{y0} ≤ {f} {n0}" else s!"{f} {n0} ≤ {y0}"
    ([("record", s!" SqueezeBench.patch {cur} {n0} {y0}"),
      ("valid", s!"\n  SqueezeBench.patch_valid{prime} {curValid} (by\n    -- the mathematics: `{math}`\n    sorry)"),
      ("improves", s!"\n  SqueezeBench.patch_improves{prime} (by decide)"),
      ("strict", s!"\n  SqueezeBench.patch_strict{prime} (by decide) (by decide)")], "", "")
  | some "fold" =>
    let n0 := match at? with | some n => toString n | none => "<n0>"
    let pad := if lower then
        s!"\n-- A lower bound must vanish below `nMin`: write `SqueezeBench.pin {nmin} (fun n => ...)` and prove\n-- `v_valid` with `SqueezeBench.pin_lowerBoundHolds` (CONTRIBUTING, \"Pad your lower bounds\")."
      else ""
    let defHelper := s!"-- Your bound, in ℕ arithmetic (CONTRIBUTING, \"Two traps\").{pad}\ndef v : SqueezeBench.BoundFn := fun n => sorry\n\n"
    let proofHelper := s!"theorem v_valid : {t.holdsName} {f} v := by\n  sorry\n\n"
    ([("record", s!" SqueezeBench.{fold} {cur} v"),
      ("valid", s!"\n  SqueezeBench.{fold}_valid {curValid} v_valid"),
      ("improves", s!"\n  SqueezeBench.{fold}_improves"),
      ("strict", s!"\n  -- once `v` is defined, replace the `sorry` with:\n  -- SqueezeBench.{fold}_strict (nMin := {nmin}) (n₀ := {n0}) (by decide) (by decide)\n  sorry")],
     defHelper, proofHelper)
  | _ => ([], "", "")

private def holes : List String := ["record", "valid", "improves", "strict"]

/-- The hole a line begins, if it is `def record …` or `theorem valid|improves|strict …`. -/
private def holeStart (line : String) : Option String :=
  holes.find? fun h =>
    let starts (kw : String) := line.startsWith s!"{kw} {h}" &&
      match (line.dropS s!"{kw} {h}".length).front with
      | c => !(c.isAlphanum || c == '_' || c == '.')
    starts "def" || starts "theorem"

/-- The four holes of the open Challenge, each with its `sorry` replaced, keyed by hole name. -/
def holeTexts (challengeSrc : String) (t : Track) (k : Nat) (bodies : List (String × String)) :
    Except String (List (String × String)) := do
  let ns := t.ns k
  let lines := challengeSrc.splitOn "\n"
  let some i0 := lines.findIdx? (·.trimS == s!"namespace {ns}")
    | throw s!"{t.challenge k} does not open namespace {ns}"
  let some i1 := lines.findIdx? (·.trimS == s!"end {ns}")
    | throw s!"{t.challenge k} does not close namespace {ns}"
  let body := (lines.drop (i0 + 1)).take (i1 - i0 - 1)
  let mut out : List (String × String) := []
  let mut current : Option (String × Array String) := none
  for line in body do
    match current with
    | some (h, acc) =>
      if line.trimEndS.endsWith ":= sorry" then
        let stem := line.trimEndS.dropEndS " sorry".length
        out := out ++ [(h, "\n".intercalate (acc.push (stem ++ (bodies.lookup h).getD " sorry")).toList)]
        current := none
      else current := some (h, acc.push line)
    | none =>
      if let some h := holeStart line then
        if line.trimEndS.endsWith ":= sorry" then
          let stem := line.trimEndS.dropEndS " sorry".length
          out := out ++ [(h, stem ++ (bodies.lookup h).getD " sorry")]
        else current := some (h, #[line])
  unless holes.all (fun h => (out.lookup h).isSome) do
    throw s!"{t.challenge k}: expected the four holes, found {out.map (·.1)}"
  pure out

/-! ## The command -/

def run (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with | .ok o => pure o | .error e => die e
  if opts.help then IO.println usage; return 0
  let _ ← root
  let tty ← (← IO.getStdin).isTty
  let guided := args.isEmpty
  let known ← problems
  let problem ← resolve opts.problem none s!"problem ({" ".intercalate known.toList})"
    "no problem given (try --help)" (validateProblem known) tty guided
  let cfg ← ProblemConfig.load (FilePath.mk "Challenges" / problem / "problem.toml")
  let direction ←
    if opts.direction.isNone && cfg.directions.size == 1 && !(guided && tty) then
      pure cfg.directions[0]!
    else
      resolve opts.direction (if cfg.directions.size == 1 then cfg.directions[0]? else none)
        s!"direction ({" or ".intercalate cfg.directions.toList})"
        "no direction given (try --help)" (validateDirection cfg) tty guided
  let t : Track := { problem, dir := direction }
  let name ← resolve opts.name (← gitConfig "user.name") "name (the public credit)"
    "no --name and no git user.name; set one with `git config --global user.name \"Your Name\"`"
    (validateNonEmpty "name") tty guided
  let idiom ← match opts.idiom with
    | some i => match validateIdiom i with
      | .ok "none" => die "--idiom must be patch or fold, not 'none'"
      | .ok i => pure i
      | .error e => die e
    | none => if guided && tty then ask "idiom (none, patch, fold)" (some "none") validateIdiom else pure "none"
  let idiom? := if idiom == "none" then none else some idiom
  let validateAt (s : String) : Except String String := do
    let s ← validateNat "--at" s
    if s.toNat! < cfg.nMin then
      throw s!"--at {s} is below {problem}'s nMin = {cfg.nMin}; the witness must satisfy n0 ≥ nMin"
    pure s
  let atRaw ← match opts.at?, idiom? with
    | some s, _ => pure (some s)
    | none, some "patch" => if guided && tty then some <$> ask "witness n0 (the n at which your record beats the previous one)" none validateAt else pure none
    | none, some "fold" =>
      if guided && tty then
        let s ← ask "witness n0, if already known (the n at which your record beats the previous one)" (some "")
          (fun s => if s.isEmpty then .ok s else validateAt s)
        pure (if s.isEmpty then none else some s)
      else pure none
    | none, _ => pure none
  let valueRaw ← match opts.value?, idiom? with
    | some s, _ => pure (some s)
    | none, some "patch" => if guided && tty then some <$> ask "the new value at n0" none (validateNat "--value") else pure none
    | none, _ => pure none
  match idiom? with
  | some "patch" => if atRaw.isNone || valueRaw.isNone then die "--idiom patch needs --at <n0> and --value <y0>"
  | some "fold" => if valueRaw.isSome then die "--value is for --idiom patch; a fold's witness is --at alone"
  | _ => pure ()
  let at? ← match atRaw with
    | some s => match validateAt s with | .ok s => pure (some s.toNat!) | .error e => die e
    | none => pure none
  let value? ← match valueRaw with
    | some s => match validateNat "--value" s with | .ok s => pure (some s.toNat!) | .error e => die e
    | none => pure none
  let some k ← t.openVersion | die s!"{t.challengeDir} holds no Challenge; the track is not open"
  let cur ← t.currentVersion
  unless cur == some (k - 1) && k ≥ 1 do
    die s!"the open Challenge is {vtag k} but the standing record is {(cur.map vtag).getD "none"}; run `lake exe squeeze accept {problem} {direction}` first"
  let dest := t.recordDir k
  if ← dest.pathExists then die s!"{dest} already exists"
  let (bodies, defHelper, proofHelper) := holeBodies t k idiom? at? value?
  let texts ← match holeTexts (← IO.FS.readFile (t.challenge k)) t k bodies with
    | .ok s => pure s | .error e => die e
  let ns := t.ns k
  let get (h : String) := (texts.lookup h).getD ""
  let defFile := s!"import {t.recordModule (k - 1)}.Def

/-! Record {vtag k} for {problem}, {direction} direction, by {name}: the record function.
Keep the statement of `record` as written; it is copied from
`{t.challenge k}`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace {ns}

{defHelper}{get "record"}

end {ns}
"
  let proofFile := s!"import {t.recordModule k}.Def
import {t.recordModule (k - 1)}.Proof

/-! Record {vtag k} for {problem}, {direction} direction, by {name}: the three obligations.
Keep the statements as written; they are copied from
`{t.challenge k}`. -/

namespace {ns}

{proofHelper}{get "valid"}

{get "improves"}

{get "strict"}

end {ns}
"
  let md : Metadata := { name := some name, witness := at?, expect := none }
  IO.FS.createDirAll dest
  IO.FS.writeFile (dest / "Def.lean") defFile
  IO.FS.writeFile (dest / "Proof.lean") proofFile
  IO.FS.writeFile (dest / "metadata.toml") md.render
  IO.FS.writeFile (dest / "REPORT.md") (reportTemplate problem direction (vtag k) name)
  let idiomNote := match idiom? with | some i => s!", idiom: {i}" | none => ""
  IO.println s!"created {dest}/  ({problem} {direction}, answering {t.challenge k}{idiomNote})"
  note "Def.lean        fill in `record`; only plain definitions may live here"
  note "Proof.lean      fill in the sorry(s); the statements are the Challenge's, do not edit them"
  let w := match at? with | some n => s!"witness = {n}" | none => "set witness once you know your n0"
  note s!"metadata.toml   credited as \"{name}\"; {w}"
  note "REPORT.md       how you obtained the bound and the proofs, and your setup (models, machine)"
  IO.println "next:"
  note s!"lake build {t.recordModule k}.Proof"
  note s!"lake exe squeeze verify {dest}          # Linux; after lake exe squeeze bootstrap"
  note s!"open a pull request adding only {dest}/"
  return (0 : UInt32)

end SqueezeBench.Tool.New
