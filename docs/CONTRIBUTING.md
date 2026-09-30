# Contributing to SqueezeBench

You improve a problem's **record**: a Lean function `ℕ → ℕ` with a machine-checked proof that
it bounds `f`. This file explains what to write, how to submit it, and how it is checked.

## How it works

Each problem has two tracks, `Lower` and `Upper`, numbered independently: `V000`, `V001`, …
For the next version of a track the repository holds a **Challenge**,
`Challenges/<Problem>/<Direction>/V<k>.lean`. It fixes four declarations and leaves them open:

```lean
namespace SqueezeBench.Golomb.Upper.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V000.record record := sorry

end SqueezeBench.Golomb.Upper.V001
```

You fill them in. For a lower record against the previous record `prev`:

| declaration | meaning |
|---|---|
| `record` | your bound, a function `ℕ → ℕ` |
| `valid` | it bounds `f`: `∀ n, record n ≤ f n` |
| `improves` | it is no worse anywhere: `∀ n, prev n ≤ record n` |
| `strict` | it is better somewhere: `∃ n₀ ≥ nMin, prev n₀ < record n₀` |

Upper records reverse the inequalities. Only `valid` is mathematics. The idioms below make
`improves` and `strict` one line each.

Your submission is one new directory. When it is merged, that directory *is* the record:

```
SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k>/
├── Def.lean          -- `def record`, and nothing but definitions
├── Proof.lean        -- `valid`, `improves`, `strict`, and any helpers
├── metadata.toml     -- your name, the witness, and the versions you built on
└── REPORT.md         -- how you obtained the record, your setup and your sources
```

A worked example is `SqueezeBench/Problems/Tutorial/Records/Lower/V001/` (patch idiom);
`Fixtures/Tutorial/Bob/` shows the `maxWith` idiom.

## Submitting, step by step

`<Problem>` is the problem, `<Direction>` is `Lower` or `Upper`, `V<k>` is the open version (the
highest Challenge in the tree). Run everything from the project root.

**1. Fork and clone.**

```sh
gh repo fork leansolving/SqueezeBench --clone     # or fork on GitHub, clone, and add `upstream`
cd SqueezeBench
```

**2. Set up, once per machine.** The requirements are in the [README](../README.md).

```sh
lake exe cache get           # prebuilt Mathlib
lake build
lake exe squeeze bootstrap   # the verifier tools; Linux only, needs cargo
```

**3. Branch from the current `main`.**

```sh
git fetch upstream
git checkout -b <branch> upstream/main
```

**4. Lay out the record.** The tool asks for anything you leave out; `--help` lists the options.

```sh
lake exe squeeze new <Problem> <lower|upper>
lake exe squeeze new Golomb upper --name "Alice Smith" --idiom patch --at 7 --value 25   # all at once
```

It writes the four files with the namespace and statements copied from the Challenge. With
`--idiom patch` or `--idiom fold` it also writes the record and the mechanical proofs, and
leaves you the mathematics.

**5. Write the record.** Fill in `Def.lean`, `Proof.lean`, `REPORT.md` and the `witness` in
`metadata.toml`, then build:

```sh
lake build SqueezeBench.Problems.<Problem>.Records.<Direction>.V<k>.Proof
```

**6. Commit your directory and nothing else.**

```sh
git add SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k>
git commit -m "<Problem> <Direction> V<k>"
```

**7. Verify.** This is the command the maintainers run. It must end with exit code 0. Exit
code 3 means someone landed first; see *Rebasing*.

```sh
lake exe squeeze verify SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k> --base upstream/main
```

**8. Open the pull request.**

```sh
git push -u origin <branch>
gh pr create --repo leansolving/SqueezeBench --base main
```

**9. Wait for the review.** A maintainer runs the same verification from a fresh checkout,
reads your `REPORT.md` and merges. To change something, push to the same branch.

## The four files

**`Def.lean`** holds `record`. The next Challenge imports this file, so it may contain only
plain `def` and `abbrev` (plus doc comments, `open`, `set_option`, `namespace … end`). It may
import only Lean, Mathlib, `SqueezeBench.Core`, the problem's `Def` and `Finite`, and the
previous version's `Def.lean`.

**`Proof.lean`** holds the three theorems and your helpers. It imports your `Def.lean` and
the previous version's `Proof.lean`.

In both files, keep the statements exactly as the Challenge has them:

- **Copy the types verbatim.** `record : BoundFn` and `record : ℕ → ℕ` are not
  interchangeable; the second fails the check.
- **Keep the names fully qualified.** If you `open SqueezeBench.Golomb` and your file defines
  its own `f`, your theorem is about your `f` and is rejected.

**`metadata.toml`**:

```toml
name     = "Alice Smith"     # how you are credited
witness  = 7                 # one n₀ ≥ nMin where your record beats the previous one
based-on = ["V001"]          # versions whose code you reused; "<Problem>/<Dir>/V<k>" for another track
```

Give one witness even if you improve everywhere. Choose an `n` that is cheap to evaluate.

**`REPORT.md`** says how you found the bound and its proofs (by hand, with an AI agent, with
automation), from which sources, and your setup: models and agents, machine, time spent, and
any computation outside Lean. The reviewer reads it before merging.

## Idiom 1 — improve at a point

You have a better bound at one `n`. Patch the record there. Here `prev` is
`SqueezeBench.<Problem>.<Direction>.V<k-1>.record` and `prev_valid` is the `.valid` beside it.

```lean
-- Def.lean
def record : SqueezeBench.BoundFn := SqueezeBench.patch prev 29 585

-- Proof.lean
theorem valid    : SqueezeBench.LowerBoundHolds SqueezeBench.<Problem>.f record :=
  SqueezeBench.patch_valid prev_valid (by  /- your proof that 585 ≤ f 29 -/ )
theorem improves : SqueezeBench.ImprovesLower prev record := SqueezeBench.patch_improves (by decide)
theorem strict   : SqueezeBench.StrictlyImprovesLower SqueezeBench.<Problem>.nMin prev record :=
  SqueezeBench.patch_strict (by decide) (by decide)
```

Upper bounds use `patch_valid'`, `patch_improves'`, `patch_strict'`.

## Idiom 2 — fold in an unrelated bound

You have a bound `v` that beats the record somewhere, and you do not know how it compares
elsewhere. Take the pointwise max; then `improves` holds unconditionally.

```lean
-- Def.lean
def v : SqueezeBench.BoundFn := fun m => /- your bound -/
def record : SqueezeBench.BoundFn := SqueezeBench.maxWith prev v

-- Proof.lean
theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.<Problem>.f v := by /- your proof -/
theorem valid    : SqueezeBench.LowerBoundHolds SqueezeBench.<Problem>.f record := SqueezeBench.maxWith_valid prev_valid v_valid
theorem improves : SqueezeBench.ImprovesLower prev record := SqueezeBench.maxWith_improves
theorem strict   : SqueezeBench.StrictlyImprovesLower SqueezeBench.<Problem>.nMin prev record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.<Problem>.nMin) (n₀ := /- your n₀ -/) (by decide) (by decide)
```

Upper bounds use `minWith` and its lemmas.

## Idiom 3 — a wholesale closed form

If you can prove that your function dominates the record everywhere, submit it directly and
prove `improves` yourself. The record is cleaner, but there is no automation for it. If the
proof resists, use Idiom 2.

## Pad your lower bounds below `nMin`

`f` is `0` below the problem's `nMin`, and `valid` quantifies over every `n`. So a lower
record must be `0` there too: `fun n => 2 ^ n` is never a valid lower record, because it is
`1` at `n = 0`. Use `pin`:

```lean
def record : SqueezeBench.BoundFn := SqueezeBench.pin SqueezeBench.<Problem>.nMin (fun n => /- your bound, valid for n ≥ nMin -/)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.<Problem>.f record :=
  SqueezeBench.pin_lowerBoundHolds (by intro n hn; /- your proof, with `hn : nMin ≤ n` -/)
```

Upper bounds need no padding.

## Two traps that will cost you time

**Write the record in ℕ arithmetic.** The verifier and later submitters compare records by
`decide`. `Nat` reduces fast in the kernel; `Rat` gets plain `decide` stuck. If your bound is
naturally rational (`2.2202ⁿ`, say), expose a ℕ-valued function.

**Keep evaluation cheap.** `squeeze verify` evaluates your record in the kernel, by
`decide +kernel`: at your witness against the previous record, and at every `n` from `nMin` to
the problem's `fuel-range-max` (default 100). Each check runs under the problem's
`fuel-budget-heartbeats` with memory capped at 8 GB. A record that searches for `f` fails
here. So does one with huge intermediates: `22202^n / 10000^n` exhausts the budget; use a
recurrence instead.

## Rules your submission must satisfy

`squeeze verify` checks all of these except the last.

- The pull request adds your record directory and touches nothing else.
- It builds against the pinned toolchain.
- No `sorry`, `admit`, new `axiom`, or native evaluation (`native_decide`, `bv_decide`,
  `bv_check`). The axioms of the three theorems lie inside
  `{propext, Classical.choice, Quot.sound}`. Every proof is checked by the kernel, so a SAT
  certificate checked by compiled code is rejected too.
- `Def.lean` holds only definitions and the allowed imports (see *The four files*).
- `record` is computable and its definition does not mention `f` or any constant the problem
  lists as an oracle. Your proofs may mention `f` freely.
- The statements match the Challenge, including the problem's own `nMin` in `strict`.
- `Def.lean` is at most 64 KB and the directory at most 1 MB, unless `problem.toml` says
  otherwise.
- Comparator finishes within 30 minutes and 16 GB of memory.
- `Proof.lean` keeps to the computation budget below.
- Outside code and data are licensed compatibly and listed in `REPORT.md` (checked at review).

Verification is **Linux-only** and must not run as root. On macOS or Windows you can build
your proofs, but `verify` has to run on Linux.

## How your submission is verified

`lake exe squeeze verify` first checks that your version is still the open one. If not, it
stops with exit code 3 (see *Rebasing*). Then it runs six gates, in order:

1. **Diff restriction.** The pull request touches nothing outside your record directory.
   Skipped when you run `verify` without `--base`.
2. **Size limits and the `Def.lean` check.** The file is parsed, not run: only plain `def`
   and `abbrev`, only the allowed imports.
3. **Comparator.** See below. Limited to 30 minutes and 16 GB.
4. **Computation budget.** `Proof.lean` is elaborated again with the heartbeats counted,
   under 8 GB.
5. **Admissibility.** `record` is computable and its definition reaches neither `f` nor any
   oracle in `Challenges/<Problem>/problem.toml`.
6. **Fuel budget.** The kernel evaluates your record at the witness and at every `n` from
   `nMin` to `fuel-range-max`.

Exit codes: `0` accepted, `1` rejected, `2` wrong arguments or missing tools, `3` rebase
needed.

[Comparator](https://github.com/leanprover/comparator) is the judge, used unmodified. It
builds the Challenge and your record in sandboxes and compares them. When it succeeds:

- your four declarations have exactly the types the Challenge states;
- everything those types mention (`f`, `nMin`, the previous record) is unchanged, so a local
  `f` that shadows the real one is caught;
- the proofs use no axiom outside `propext`, `Quot.sound` and `Classical.choice`;
- two independent kernels accept the proofs: Lean's own and
  [nanoda](https://github.com/robsimmons/nanoda_lib).

Comparator alone is not enough. `def record := f` passes it: the statements match and the
proofs are true. But nobody could evaluate that record, so nobody could ever beat it. Gates 5
and 6 exist for this. A record must be computable, must not be `f` under another name, and
must be cheap at every small `n`, so the next submitter can build on it.

## Computation budget

Proofs here reason, as on paper. Computation may check data your record provides, such as a
construction or a small table. It may not search (every subset, every colouring, every
ruler), however the search is split up. `squeeze verify` enforces this by measurement:

- each declaration of `Proof.lean` runs under 200000 heartbeats, and so does the whole file
  in total;
- `set_option` is allowed for `linter.*` and `pp.*` only, so you cannot raise the limit;
- no command or attribute that runs code at elaboration time (`#eval`, `run_cmd`, `elab`,
  `macro`, `syntax`, `notation`, `@[tactic]`, `@[init]`, …). Allowed attributes are `simp`,
  `instance`, `ext`, `reducible`, `irreducible`, `semireducible` and `inline`.

To see where your budget goes:

```sh
lake exe squeeze budget-probe SqueezeBench/Problems/<P>/Records/<Dir>/V<k>/Proof.lean
```

## Rebasing

If someone else lands first, `V<k+1>` is now the open version and `squeeze verify` stops with
exit code 3 and a `REBASE:` message. Rename your directory to `V<k+1>`. In both files replace
`V<k>` by `V<k+1>` in the namespace and `V<k-1>` by `V<k>` in every reference to the previous
record. With Idiom 2 the proofs are unchanged. With Idiom 1, check `patch_improves` again at
your point.

## License and outside sources

SqueezeBench is under the Apache License 2.0 ([`LICENSE`](../LICENSE)). By opening a pull
request you license your four files under the same terms and confirm you have the right to.

You may build on other people's work:

- **Code** from outside this repository must be under Apache-2.0, MIT or BSD. GPL,
  non-commercial, no-derivatives and unlicensed code cannot be accepted.
- In each file with such code, keep the original copyright notices and add a comment naming
  the source and saying that you changed it. For a license other than Apache-2.0, add a copy
  to `LICENSES/`. If the source has a `NOTICE` file, copy its notices into `REPORT.md`.
- **Data**, such as a table of values, a graph or a cap, may be used with a citation.
- List every outside source under `## Sources` in `REPORT.md`: the URL pinned to a commit or
  version, the license, and what you took. This includes code an AI system retrieved for you.
- Code reused from earlier versions in this repository goes in `based-on` in `metadata.toml`.

## After the merge

A maintainer runs `lake exe squeeze accept`. It opens the next Challenge and adds a row to the
problem README's *Record history*: the date, your name, the versions you built on, your
witness, and the value before and after.
