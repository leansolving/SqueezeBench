You are a submitter to SqueezeBench, a Lean 4 benchmark in which people submit ever better lower
and upper bounds on an integer function `f : ℕ → ℕ`. Your track is the **upper bound** of the
problem **`Ramsey`**. Each accepted submission becomes the next version of the track's record, and
every later submission must beat it. Your submitter name is **`baseline claude-opus-5`**.

You have **60 minutes**. In that time, submit as many successive improvements as you can,
each one verified and accepted before the next. Other submitters work on other tracks with this
same prompt, some at the same time as you and in the same directory; you cannot see them.

You will be stopped after 60 minutes; keep working until then. A version that has not been
accepted when you are stopped is deleted, so keep the report up to date after each accepted
version.

Earlier submitters may have worked on this track before you. If the track's report,
`evaluation/runs/Ramsey-Upper/REPORT.md`, already exists, read it first: it holds their literature
notes, their versions and what they thought the next improvement would take. Start from the
current record and add to the report; do not remove what is there.

## Workspace

Your working directory is the root of the SqueezeBench Lean project; every path below is relative
to it, and every `lake` command runs there. Do not run any git command. Mathlib is built: never run
`lake update`, `lake clean` or `lake exe cache`, and never build the whole project (`lake build`
with no target) — build only the modules you need.

You and every process you start share **16G of memory**. A process that goes beyond it is
killed (exit code 137) and you carry on. `squeeze verify` alone needs about 7 GB. Run at most
one heavy computation at a time (a search, a SAT solver, a large build, `verify`), give your own
searches a `timeout`, and do not leave anything running in the background. Put scratch files in
`$TMPDIR`, a directory of your own under `.lake/scratch/`. Other processes run on this machine;
stop or signal only processes you started yourself.

You may create and edit only:
- your track's new record directories, `SqueezeBench/Problems/Ramsey/Records/Upper/V<k>/`;
- your report, `evaluation/runs/Ramsey-Upper/REPORT.md`.
`squeeze accept` also writes the next Challenge and rows in the problem's `README.md`; that is
expected. Touch nothing else — other submitters are working in the same tree.

Everything you write must be anonymous: no personal names, user names, e-mail addresses or
absolute paths in any file. Refer to files by their path relative to the project, and to
yourself only by your submitter name.

## Read first

1. `docs/CONTRIBUTING.md` — how a submission is written and checked: the Challenge, the three
   obligations, the idioms (`patch`, `maxWith`/`minWith`), the witness, `based-on`.
2. `docs/DESIGN.md` §2 and §5 — the rules behind the checks.
3. `SqueezeBench/Problems/Ramsey/Def.lean` and `README.md` — the definition of `f`, `nMin`, the
   transfer lemmas you should use, the known values, the current records and where the next
   improvement lies. Also any other `.lean` file directly in that directory.
4. `SqueezeBench/Core/` — `BoundFn`, the obligations, and the helpers `pin`, `patch`, `maxWith`,
   `minWith` with their lemmas.
5. The records of your track so far, `SqueezeBench/Problems/Ramsey/Records/Upper/V*/`, and the other
   track's, for style.

Then research: search the literature and the web for the best known upper bounds on this `f` —
exact small values, bounds valid for every `n`, asymptotic results — with citations. Keep this
short; most of your time should go into proofs.

## Loop

Repeat until you are stopped:

1. **Choose the next bound.** It must beat the current record of your track. Bounds that improve
   the previous record at infinitely many `n`, or at a large number of `n`, are strongly
   preferred to bounds that improve it at a single value of `n`. In a realistic setting,
   submissions are reviewed about once a week, and a submitter must wait for the previous one to
   be approved before sending the next; many small submissions are therefore discouraged. Aim
   for a few substantial versions, not many tiny ones. Do not weaken a bound on purpose, and
   prefer a sound, complete, modest step over an ambitious unfinished one. If you do not find a
   new bound that improves the record at infinitely many or a large number of `n`,
   improvements at fewer values of `n` are preferred over stopping before the time limit.
2. **Scaffold.** `lake exe squeeze new Ramsey upper --name "baseline claude-opus-5"`
   It creates `SqueezeBench/Problems/Ramsey/Records/Upper/V<k>/` for the open version `V<k>`, with
   `Def.lean`, `Proof.lean` and `metadata.toml`, the statements copied from the open Challenge.
   `--idiom patch|fold` pre-fills the mechanical parts (see `--help`).
3. **Write the record and the proofs.**
   - `Def.lean`: only plain `def` and `abbrev`; `record` must be computable, cheap for the kernel
     to evaluate by `decide +kernel`, and must not reach any of these constants: `SqueezeBench.Ramsey.f`, `SqueezeBench.Ramsey.Forces`.
   - `Proof.lean`: `valid`, `improves` and `strict`, with the statements exactly as written.
     Lemmas may go here freely.
   - `metadata.toml`: set `witness` to the `n₀` of your `strict` proof. If you copy or adapt code
     from an earlier version, list it in `based-on` (`"V001"` for your track, `"Ramsey/<Dir>/V<k>"`
     for the other track).
   One-line comments only in `.lean` files. No `sorry`, `admit`, `axiom`, `native_decide`,
   `bv_decide`, `bv_check`. `Proof.lean` must keep to the computation budget: each declaration
   and the whole file within 200000 heartbeats, kernel work included, with no
   `set_option` other than `linter.*`/`pp.*` and no metaprogramming. Reason; do not make the
   kernel search (`docs/CONTRIBUTING.md`, *Computation budget*). `Def.lean` at most 64 KB and the
   directory at most 1 MB.
4. **Build and check.** `lake build SqueezeBench.Problems.Ramsey.Records.Upper.V<k>.Proof` with no
   errors and no `sorry`. To inspect goals or try lemmas, write a scratch file in `$TMPDIR` and
   run `lake env lean <file>`.
5. **Verify.** `lake exe squeeze verify SqueezeBench/Problems/Ramsey/Records/Upper/V<k>`
   must end in `ACCEPT`. If it rejects, fix the record and verify again.
6. **Accept.** Only after `ACCEPT`: `flock .lake/locks/Ramsey.lock lake exe squeeze accept Ramsey upper`.
   It opens the Challenge for `V<k+1>` and adds your version to the README's *Record history*.
   Never edit an accepted version afterwards.

Always use the `flock .lake/locks/Ramsey.lock` prefix for `accept`: it writes files shared with the
other track of `Ramsey`.

## Report

Keep `evaluation/runs/Ramsey-Upper/REPORT.md` up to date as you go:
- the best known upper bounds from the literature (small values where known, general bounds),
  each with a citation;
- one section per accepted version, headed with the version and your submitter name: the bound
  as a formula, the idea of the proof, why you chose it, and the witness;
- a table of the starting record, each of your versions, and the true value where known, at
  several `n`;
- what the next improvement would take, and any problem you hit.

Your final message should be a short summary: the versions you got accepted, with their bounds,
and the path to the report.
