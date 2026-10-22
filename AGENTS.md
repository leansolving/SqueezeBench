# AGENTS.md

This file is for an AI agent asked to improve a SqueezeBench record. People should start with `README.md`. The authoritative rules are in `docs/CONTRIBUTING.md`; if this file and CONTRIBUTING disagree, CONTRIBUTING wins.

## The task

Each problem is a function `f : ℕ → ℕ` from extremal combinatorics and has two tracks, `Lower` and `Upper`. Each track holds a record: a computable Lean function with a proof that it bounds `f`. You improve one track by adding the next version `V<k>`, a new function with three proofs: `valid` (it bounds `f`), `improves` (no worse than the current record at any `n`) and `strict` (better at some `n₀ ≥ nMin`). The statements are fixed by the open Challenge `Challenges/<Problem>/<Direction>/V<k>.lean`, the highest version in that directory. Your submission is one new directory, `SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k>/`, sent as a pull request.

## Read first, in this order

1. `README.md`: the problems and the current record of each track.
2. `docs/CONTRIBUTING.md`, all of it: the steps, the four files, the idioms, the traps, the rules.
3. `SqueezeBench/Problems/<Problem>/README.md` and `Def.lean`: the definition of `f`, `nMin`, the known values, the record history and the lemmas the problem provides.
4. `Challenges/<Problem>/problem.toml`: the oracles your record must not use, `fuel-budget-heartbeats` and `fuel-range-max` (default 100 when absent).
5. The open Challenge and the current record `Records/<Direction>/V<k-1>/`, with its `REPORT.md`.
6. `evaluation/runs/<Problem>-<Direction>/REPORT.md`: notes from the agents of our baseline runs on this track, with the literature, each version and what the next improvement would take. Often the fastest way to see where the record stands.
7. `SqueezeBench/Core/`: `BoundFn`, the obligations and the helpers `pin`, `patch`, `maxWith`, `minWith`.
8. A recent accepted record of your track as the template for all four files. Follow the current rules where an older record does not: many records predate them and have no `REPORT.md`, or no `## Sources` heading in it. The Tutorial record `SqueezeBench/Problems/Tutorial/Records/Lower/V002/` shows the `patch` idiom in its simplest form and follows the current format.

**The evaluation reports** are kept as the agents wrote them during our runs: they can mention unaccepted record directories and scratch files under `.lake/` that are not in the repository, and steps such as `squeeze accept` that only maintainers run. Use them for the mathematics and the literature, not for the workflow.

## Choosing what to do

- If the human named a problem and direction, work on that track. Otherwise propose one and say why, for example a track whose report names a published bound that is not yet formalized.
- Compare the current record with the literature first. Most records are behind published bounds, so formalizing a known result is a legitimate submission; cite it in `REPORT.md`. Check the statement against the paper itself, not only against a summary in a report.
- Prefer a bound that beats the record at infinitely many `n` or over a long range to one that wins at a single `n`. Prefer a sound, complete, modest step to an ambitious unfinished one.

## Workflow

The commands are in CONTRIBUTING, *Submitting, step by step*, which also covers the fork. You need `git`, `elan`, the GitHub CLI `gh`, and for verification a C compiler and `cargo`. The commands below assume a fork cloned as `origin` with this repository as `upstream`. If you start from a plain clone of this repository, rename its remote to `upstream` and add the fork as `origin` once the human has approved the fork.

```sh
lake exe cache get && lake build              # once per machine
lake exe squeeze bootstrap                    # once per machine; Linux only, needs cargo
git fetch upstream && git checkout -b <branch> upstream/main
lake exe squeeze new <Problem> <lower|upper> --name "<credit name>"
lake build SqueezeBench.Problems.<Problem>.Records.<Direction>.V<k>.Proof
lake exe squeeze budget-probe SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k>/Proof.lean
git add SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k> && git commit -m "<Problem> <Direction> V<k>"
lake exe squeeze verify SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k> --base upstream/main
```

- Never run `lake update` or `lake clean`, and do not change `lean-toolchain`, `lakefile.toml` or `lake-manifest.json`. If a tool message tells you to, stop and ask the human.
- `squeeze bootstrap` and `squeeze verify` run only on Linux with Landlock, not as root, and Comparator may use up to 16 GB. On macOS or Windows you can build and run `budget-probe`, but the human has to provide a Linux machine for `verify` before the pull request.
- To test a lemma or look at a goal, write a scratch file outside the record directory, run `lake env lean <file>`, and never commit it. `#check_admissible` belongs in such a scratch file, not in the submission.

## Rules that reject a submission

CONTRIBUTING, *Rules your submission must satisfy*, is the full list. The ones agents break most:

- Commit nothing outside your record directory.
- Copy the Challenge's statements verbatim, with fully qualified names.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide` or `bv_check`. Axioms only from `propext`, `Classical.choice`, `Quot.sound`.
- `Def.lean` holds only `def` and `abbrev`. `record` is computable, never mentions `f` or an oracle, uses ℕ arithmetic and is cheap for `decide +kernel` at every `n` from `nMin` to `fuel-range-max`. A lower record is `0` below `nMin` (use `pin`).
- `Proof.lean` stays within 200000 heartbeats per declaration and for the whole file, with no `set_option` beyond `linter.*` and `pp.*` and no metaprogramming. Proofs reason; computation may only check data the record provides, never search.
- Outside code only under Apache-2.0, MIT or BSD, listed under `## Sources` in `REPORT.md`. If a license file would have to go into `LICENSES/`, ask the human first: that is outside your directory.

## Ask the human

- for the credit name in `metadata.toml` if you were not given one;
- before forking, pushing or opening the pull request, since these publish your work;
- for a Linux machine if you cannot run `verify`;
- when a rule is unclear. Do not guess a reading that would let a weaker proof through.

## Before the pull request

- The module builds with no errors and no `sorry` warnings.
- `budget-probe` reports a total below 200000.
- `verify` exits with `0` on the commit you push. Exit code `3` means someone landed first: rebase as in CONTRIBUTING, *Rebasing*, then check that your witness still beats the new record and verify again.
- `git status` shows changes only inside your record directory.
- `REPORT.md` says how the bound was found, the model and agent, the machine, the time spent and the sources; `metadata.toml` has the witness and `based-on`.
- The maintainers merge and run `squeeze accept`; you do not.
