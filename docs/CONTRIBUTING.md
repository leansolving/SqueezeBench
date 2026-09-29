# Contributing to SqueezeBench

You improve a problem's **record**: a Lean function `ℕ → ℕ` together with a machine-checked
proof that it bounds `f`. A submission is a new function that is still a bound, does not
regress anywhere, and is **strictly better at at least one `n`**.

[`DESIGN.md`](DESIGN.md) states the rules; this file is the practical walkthrough. Run every
command below from the project root; paths are relative to it.

## What you submit

A submission is the next record version itself, added in place:

```
SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k>/
├── Def.lean          -- the record function: `def record`, and nothing but definitions
├── Proof.lean        -- the three obligations, and any helpers
├── metadata.toml     -- your name, and the witness
└── REPORT.md         -- how you obtained the record, and your setup
```

`V<k>` is the **open version**: the highest `Challenges/<Problem>/<Direction>/V<k>.lean` in
the tree. Everything below it is an accepted record, and `V<k>` is the one you are writing.
When your pull request is merged, your directory *is* the record; nothing is moved, renamed
or rewritten. What was verified is what stays.

Let the tool lay this out for you:

```sh
lake exe squeeze new
```

It asks for the problem, the direction, your credit name and an idiom, then writes
`Def.lean` and `Proof.lean` with the namespace and statements copied from the Challenge, and a
`metadata.toml` with your `name`, and a `REPORT.md` template. With the `patch` or `fold` idiom it also writes the record
and the mechanical obligations of Idiom 1 or 2 below, leaving only the mathematics.

Everything the prompts ask for can also be given on the command line, as a one-liner:

```sh
lake exe squeeze new Golomb upper --name "Alice Smith" --idiom patch --at 7 --value 25
```

Anything left out is asked for; anything given is not. `lake exe squeeze new --help` lists the
options.

**Your pull request must add your directory and touch nothing else.** Verification builds the
trusted statement and your record from the same tree, so this is enforced.

**Fill in `REPORT.md`.** Say how you found the bound and its proofs (by hand, with an AI
agent, with automation, and from which sources) and your setup: the models and agents used, if
any, your machine (CPU, memory, operating system), the time spent, and any computation outside
Lean. The reviewer reads it before merging (DESIGN §3.3).

**You are credited by the `name` in your `metadata.toml`.** After the merge, a maintainer
runs `lake exe squeeze accept`, which opens the next Challenge and adds a row to the problem
README's *Record history* with the date, your witness, and the value before and after.

**Credit what you reuse.** If your record copies or adapts code from an earlier version —
definitions, lemmas, proofs — list those versions in `based-on` in `metadata.toml`:
`"V001"` for a version of the same track, `"<Problem>/<Dir>/V<k>"` for another track.
`accept` shows the list next to your name in the *Record history*. Nothing can check it
automatically; the reviewer does.

There is a complete worked pair in the repository: the accepted
`SqueezeBench/Problems/Tutorial/Records/Lower/V001/` (patch idiom) and the fixture
`Fixtures/Tutorial/Bob/` (`maxWith` idiom).

## The Challenge fixes your statement

You do not write the statements. For each version of each problem and direction the
repository carries a trusted **Challenge**, `Challenges/<Problem>/<Direction>/V<k>.lean`,
which declares the record as a hole and states the three obligations against it, naming
the previous record by version:

```lean
import SqueezeBench.Core
import SqueezeBench.Problems.Golomb.Records.Upper.V000.Def

namespace SqueezeBench.Golomb.Upper.V001

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record := sorry
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V000.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V000.record record := sorry

end SqueezeBench.Golomb.Upper.V001
```

Your two files open the *same namespace* and fill the four declarations in. `record` goes
in `Def.lean`:

```lean
import SqueezeBench.Problems.Golomb.Records.Upper.V000.Def

namespace SqueezeBench.Golomb.Upper.V001

def record : SqueezeBench.BoundFn := SqueezeBench.patch SqueezeBench.Golomb.Upper.V000.record 7 25

end SqueezeBench.Golomb.Upper.V001
```

and the three theorems in `Proof.lean`, which imports your `Def.lean` and the previous
version's `Proof.lean`:

```lean
import SqueezeBench.Problems.Golomb.Records.Upper.V001.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V000.Proof

namespace SqueezeBench.Golomb.Upper.V001

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record := ...
theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V000.record record := ...
theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V000.record record := ...

end SqueezeBench.Golomb.Upper.V001
```

Two things will bite you if you improvise:

- **Copy the declared types verbatim from the Challenge.** `record : BoundFn` and
  `record : ℕ → ℕ` are *not* interchangeable — they store `SqueezeBench.BoundFn` and `Nat -> Nat`
  respectively, and unfolding the abbreviation fails the check with no obvious reason.
- **Write the statements fully qualified, as the Challenge does.** If you `open SqueezeBench.Golomb`
  and write `UpperBoundHolds f record`, and anything in your file happens to define `f`,
  your theorem is about *your* `f` and will be rejected. The check is on the elaborated
  type, so this is caught, but the error will be clearer if you never invite it.

The three obligations, for a lower record against the previous record `prev`:

```lean
theorem valid    : LowerBoundHolds f record          -- ∀ n, record n ≤ f n
theorem improves : ImprovesLower prev record         -- ∀ n, prev n ≤ record n
theorem strict   : StrictlyImprovesLower nMin prev record
                                                     -- ∃ n₀ ≥ nMin, prev n₀ < record n₀
```

Lower and upper records are separate tracks with independent version numbers, so improving
one has nothing to do with the other. Upper bounds use `UpperBoundHolds`, `ImprovesUpper`,
`StrictlyImprovesUpper`, with the inequalities reversed.

Only `valid` should ever be hard. It is the mathematics — everything else is mechanical if
you use one of the two idioms below.

## Why `Def.lean` may hold only definitions

The next Challenge imports your `Def.lean`, and commands such as `macro_rules`, `notation`,
`instance` or attributes would change what that Challenge means. So `Def.lean` holds only plain
`def` and `abbrev` (plus doc comments, `open`, `set_option`, `namespace … end`) and imports only
Lean, Mathlib, `SqueezeBench.Core`, the problem's `Def` and `Finite`, and the previous
version's `Def.lean`. `Proof.lean` may contain anything; put helpers that need attributes there.

## Idiom 1 — improve at a point

You proved a new exact value, or a better bound at one `n`. Patch the record there. With
`prev` standing for `SqueezeBench.<Problem>.<Direction>.V<k-1>.record` and `prev_valid` for the
`.valid` beside it:

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

Upper bounds use the primed lemmas `patch_valid'`, `patch_improves'`, `patch_strict'`.

## Idiom 2 — fold in an unrelated bound

You proved a bound `v` that beats the record *somewhere* but you have no idea how it
compares elsewhere. Take the pointwise max — you never have to find out:

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

`maxWith_improves` is `le_max_left` and holds unconditionally, so **obligation (ii) is never
a reason you cannot contribute**. Upper bounds use `minWith` / `minWith_improves`.

## Pad your lower bounds below `nMin`

`f` is pinned to `0` below the problem's `nMin`, but `LowerBoundHolds` quantifies over
**every** `n`. So a lower bound must vanish there too — `fun n => 2 ^ n` is *not* a valid
lower record for any problem, because it is `1` at `n = 0` where `f` is `0`. This catches
people out; the natural closed form from the literature is almost never valid as written.

Use `pin`, which does the padding and reduces the obligation to the range that matters:

```lean
def record : SqueezeBench.BoundFn := SqueezeBench.pin SqueezeBench.<Problem>.nMin (fun n => /- your bound, valid for n ≥ nMin -/)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.<Problem>.f record :=
  SqueezeBench.pin_lowerBoundHolds (by intro n hn; /- your proof, with `hn : nMin ≤ n` available -/)
```

Upper bounds need no padding: below `nMin` the goal is `f n ≤ u n` with `f n = 0`, which
holds for anything.

## Idiom 3 — a wholesale closed form

If you can prove your function dominates the record everywhere, submit it directly and
prove `improves` yourself. This produces a much cleaner record and is encouraged when the
mathematics supports it — but it is genuinely harder, and there is no automation for it.
Note that comparing two arbitrary closed forms over all `n` is not decidable in general
(`DESIGN.md` §1.2), so if the proof resists, fall back to Idiom 2.

## The witness

`witness` in `metadata.toml` is one `n₀ ≥ nMin` at which your record beats the previous one:
the `n₀` of `strict`. Even if you improve everywhere, give one witness; the "everywhere" is
carried by `improves` and by the record itself. The fuel gate evaluates both records there,
and `accept` shows the before and after values, so choose a telling `n` that is cheap to
evaluate. A record without a witness is rejected.

## Two traps that will cost you time

**Write bound functions in ℕ arithmetic.** You may prove `strict` any way you like, but
the fuel gate checks your witness comparison by `decide +kernel`, and the next submitter
will normally prove their `strict` against your record by computation too. `Nat`
arithmetic and comparison are kernel-accelerated GMP primitives and reduce fast. **`Rat` is
a trap**: plain `decide` gets stuck on `Rat.instDecidableLt`, because the elaborator cannot unfold it, while `decide +kernel` proves
the same goal. A later submitter who reaches for plain `decide` will fail. If your bound is
naturally rational (`2.2202ⁿ`, say), expose a ℕ-valued wrapper rather than making the
record itself ℚ-valued.

**Keep evaluation cheap.** `squeeze verify` runs its own probe,
`prev n₀ < record n₀ := by decide +kernel` (`>` for an upper bound) at your witness,
independent of how you proved `strict`, under `set_option maxHeartbeats` set to the problem's
`fuel-budget-heartbeats` and with Lean's memory capped at 8 GB, and rejects your record if it
fails (`DESIGN.md` §5.2 gate 5). It then settles `0 ≤ record n`, which evaluates your record,
the same way at every `n` from `nMin` to the problem's `fuel-range-max` (default 100), so your
record must be cheap at every small `n`, not only at the witness. A record that searches for
`f` fails here. Heartbeats count work, not time, so you get the same result
on your machine as the maintainer does. Note it is the
kernel, not `#eval` — a record only the compiler can evaluate blocks every submission built
on top of yours, which is the whole reason the gate exists. Writing `2.2202ⁿ` as
`22202^n / 10000^n` produces astronomically large intermediates and will exhaust the budget; use an
iterative recurrence instead. The record also delegates to its predecessor, so the chain
itself costs something.

## Rules your submission must satisfy

- Builds against the pinned toolchain (`lean-toolchain`, `lake-manifest.json`).
- No `sorry`, `admit`, fresh `axiom`, or native evaluation (`native_decide`, `bv_decide`,
  `bv_check`); see *Kernel-checked proofs only* below.
- The axiom closure of all three theorems lies inside
  `{propext, Classical.choice, Quot.sound}`.
- `Def.lean` holds only plain `def` and `abbrev`, and imports only the trusted spine and the
  previous version's `Def.lean` (see above).
- Your record function is **computable** and its definition does **not** mention `f` or any
  constant the problem marks as an oracle. (Your *proofs* may mention `f` freely — they
  must.) Submitting `record := f` is rejected here.
- The witness `n₀` satisfies `n₀ ≥ nMin`. You get this for free by copying the Challenge's
  statement, which names the problem's own `nMin`; writing a numeral there instead is
  rejected as a statement mismatch.
- `Def.lean` is at most 64 KB and your record directory at most 1 MB, unless the problem's
  `problem.toml` sets other limits (`max-def-bytes`, `max-record-bytes`).
- Comparator checks the whole submission within 30 minutes and 16 GB of memory.
- `Proof.lean` keeps to the computation budget: at most 200000 heartbeats per declaration and
  200000 for the whole file, with no `set_option` beyond `linter.*` and `pp.*`; see
  *Computation budget* below.
- Your pull request adds nothing outside your record directory.
- Outside code is under a license compatible with Apache-2.0, keeps its notices, and is listed
  with all other outside sources under `## Sources` in `REPORT.md` (checked at review; see
  *License and outside sources* below).

### How these are checked

All of it, by `lake exe squeeze verify`, which is what CI runs:

```sh
lake exe squeeze verify SqueezeBench/Problems/Golomb/Records/Upper/V001 --base main
```

It runs five gates — the diff restriction, the size limits and the `Def.lean` restriction
(parsed, never elaborated), then [Comparator](https://github.com/leanprover/comparator) (which builds your record in
a sandbox, checks it proves the Challenge's statements, checks the axioms, and replays the
proof through two independent kernels), then the admissibility gates against the problem's
own oracle list, then the fuel budget.

The same command, with `--accepted`, re-verifies every accepted record, and `lake exe squeeze audit` runs it over
all of them: the Challenge that judged your record stays in the tree, so anyone can re-run
the judgement on any clone.

You do **not** write a `#check_admissible` line. The oracle list comes from
`Challenges/<Problem>/problem.toml`, which your pull request may not touch.

Run `lake exe squeeze bootstrap` once first: it builds the pinned verifier tools (`comparator`,
`lean4export`, `landrun`, `nanoda`) into a git-ignored `.tools/`, and needs `cargo`.

**This is Linux-only.** Comparator sandboxes with `landrun`, which needs Landlock, and must
not run as root. On macOS or Windows you can still `lake build` and inspect your proofs, but
the verification itself has to happen on Linux or in CI.

## License and outside sources

SqueezeBench is licensed under the Apache License 2.0 ([`LICENSE`](../LICENSE)), the
license of Lean and Mathlib. By opening a pull request you license your submission, all four
files, under the same terms, and you confirm that you have the right to do so.

You may build on other people's work. Code taken or adapted from outside this repository must
come under a license compatible with Apache-2.0: Apache-2.0 itself, MIT or BSD. Code under the
GPL, under a non-commercial or no-derivatives license, or with no license at all cannot be
accepted. In every file that contains such code, keep the original copyright and attribution
notices and add a comment that names the source and says that you changed it. If the source
is under a license other than Apache-2.0, add a copy of that license to `LICENSES/`; if it
comes with a `NOTICE` file, copy its attribution notices into your `REPORT.md`. Mathematical
data, such as a table of values, a graph or a cap, may be used with a citation.

List every outside source of code or data in `REPORT.md` under a heading `## Sources`: the URL,
pinned to a commit or a version, the license, and what you took from it. This includes code
that an AI system retrieved for you. The maintainer checks this section at review;
`squeeze verify` does not. If undisclosed outside code turns up after acceptance, the
maintainers add the missing notices.

## Kernel-checked proofs only

Every proof must be checked by Lean's kernel. `native_decide`, `bv_decide` and `bv_check`
each add an axiom stating what compiled code returned, which no kernel can check, so
Comparator rejects a record whose theorems reach one. This includes a SAT solver's LRAT
certificate checked in Lean with compiled code. `Fixtures/Tutorial/BvCheck` and
`Fixtures/Tutorial/PlainNativeDecide` are examples of what is rejected. Why:
[`COMPARATOR.md`](COMPARATOR.md) §7.

## Computation budget

Proofs here reason, as on paper; computation may only check data your record provides. A
`decide +kernel` that checks a construction or a small table is fine; one that searches (every
subset, every colouring, every ruler) is not, however it is split up. `squeeze verify`
enforces this by measurement (`DESIGN.md` §5.6):

- each declaration of `Proof.lean` runs under 200000 heartbeats, Lean's default, and you
  cannot raise it: `set_option` is allowed for `linter.*` and `pp.*` only;
- the heartbeats of all declarations together must stay within 200000 as well, about five
  times what the heaviest baseline proof without a search needed;
- no command or attribute that runs code at elaboration time (`#eval`, `run_cmd`, `elab`,
  `macro`, `syntax`, `notation`, `@[tactic]`, `@[init]`, …); allowed attributes are `simp`,
  `instance`, `ext`, `reducible`, `irreducible`, `semireducible` and `inline`.

The kernel's work counts, so a heavy `decide +kernel` shows up. To see where your budget goes,
run the probe yourself:

```sh
lake exe squeeze budget-probe SqueezeBench/Problems/<P>/Records/<Dir>/V<k>/Proof.lean
```

It prints the heartbeats of each command and the total as JSON. If a lemma needs more, prove
it by reasoning rather than evaluation; the budget is the same for everyone and is not raised
per record.

## Rebasing

If someone else lands first, the version you wrote against is no longer open:
`Challenges/<Problem>/<Direction>/V<k+1>.lean` now exists, and `squeeze verify` stops before
any gate (exit code 3) with a `REBASE:` message rather than rejecting you. Rename your
directory to `V<k+1>`, and in both files replace `V<k>` by `V<k+1>` in the namespace line
and `V<k-1>` by `V<k>` in every reference to the previous record. For Idiom 2 the proofs
are then unchanged. For Idiom 1 you need to re-check `patch_improves` at your point against
the new record.

## Building

Requires [`elan`](https://github.com/leanprover/elan).

```sh
lake exe cache get   # prebuilt Mathlib, first time only
lake build
```

Your directory sits inside the default build target, so `lake build` compiles it; until
the holes are filled it builds with `sorry` warnings, which is expected.
