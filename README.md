# SqueezeBench

A benchmark for **Lean-verified mathematical bounds** on combinatorial extremal
problems whose answer is a single-parameter integer function `f : ℕ → ℕ`
(Schur numbers, cap sets, Ramsey numbers, Golomb rulers, Roth numbers, …).

These `f(n)` are intractable in general, known exactly only for small `n`, and
bracketed in the literature by lower/upper bounds `g(n) ≤ f(n) ≤ h(n)`. None has a known
closed form: a problem whose `f` has one would saturate, so it is not admitted
([`docs/DESIGN.md`](docs/DESIGN.md) §1).

Each problem carries two **records** — a lower-bound record and an upper-bound record.
A record is a Lean function `ℕ → ℕ` plus a machine-checked proof that it bounds `f`.
Contributors improve a record by submitting a new function together with three proofs:
that it is still a bound, that it does not regress anywhere, and that it is **strictly
better at at least one value of `n`**. The record only ever improves, and every version
of it is a theorem.

Related work already includes answer and bound holes (Formal Conjectures), best-known
optimization targets (HorizonMath, FrontierMath: Open Problems), and Lean-checked scalar
record improvement (Riemann.fail). SqueezeBench's combination is narrower: its standing
records are proved Lean functions `ℕ → ℕ`; every accepted update proves **pointwise
non-regression** and strict improvement; the same interface admits either a one-`n` patch or a
uniform/asymptotic improvement; and every admission check that can be mechanised is run by one
command, with a maintainer reviewing and merging.

See [`docs/DESIGN.md`](docs/DESIGN.md) for the specification — its **In brief** page is a
one-page summary — and [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) for the submission
walkthrough. [`evaluation/`](evaluation) holds the protocol that produced the baseline records.

> **Status:** early development. The Lean core is in place, and
> ten problems are well posed and live with seeded records in both directions.
> Submissions are judged by [Comparator](https://github.com/leanprover/comparator), unmodified,
> against a trusted statement of record frozen per version, with proofs checked by the kernel
> alone, so admission can be automated and every accepted record can be re-verified in place;
> `lake exe squeeze verify` runs the gates, `lake exe squeeze audit` re-runs them on every accepted
> record, and `lake exe squeeze new` prepares a submission. Remaining: the CI workflow that invokes
> them, and the leaderboard.

## Proven bounds

Every bound below is proved in Lean against the pinned Mathlib, with axioms ⊆
`{propext, Classical.choice, Quot.sound}` and no native evaluation. Pinning below `nMin` and
point patches (Golomb's upper record is also `11` at `m = 5` and `17` at `m = 6`) are omitted
for brevity.

| problem | `f` | lower record | upper record |
|---|---|---|---|
| [Ramsey](SqueezeBench/Problems/Ramsey) | least `N` forcing a monochromatic `K_n` | `(n−1)² + 1` | `C(2n−2, n−1)` |
| [Golomb](SqueezeBench/Problems/Golomb) | least length of an `m`-mark Sidon set | `m(m−1)/2` | `min(2^(m−1)−1, 2m³−m²−2m+1)` |
| [cap set](SqueezeBench/Problems/CapSet) | largest cap in `F₃ⁿ` | `2ⁿ` | `2·3^(n−1)` |
| [Schur](SqueezeBench/Problems/Schur) | largest `N` splitting into `k` sum-free parts | `(3^k−1)/2` | `3·k! − 2` |
| [`R(3,k)`](SqueezeBench/Problems/Ramsey3) | least `N` forcing a red `K₃` or a blue `K_k` | `2k − 1` | `C(k+1, 2)` |
| [Roth](SqueezeBench/Problems/Roth) | largest 3-AP-free subset of `{0,…,n−1}` | `min(n, 2)` | `n` |
| [Ruzsa–Szemerédi](SqueezeBench/Problems/RuzsaSzemeredi) | max triangles in a locally linear graph on `n` vertices | `1` | `C(n, 3)` |
| [`ex(n; C₄)`](SqueezeBench/Problems/ExC4) | max edges in an `n`-vertex graph with no 4-cycle | `0` | `C(n, 2)` |
| [`ex(n; {C₃,C₄})`](SqueezeBench/Problems/ExGirthFive) | max edges in an `n`-vertex graph of girth ≥ 5 | `0` | `C(n, 2)` |
| [`ex(Qₙ, C₄)`](SqueezeBench/Problems/HypercubeC4) | max edges in a `C₄`-free subgraph of the `n`-cube | `0` | `C(2ⁿ, 2)` |

Well-posedness — that the `sInf` defining `f` is taken over a nonempty set — is proved for
each problem that needs it: Golomb by the binary ruler, Ramsey by Erdős–Szekeres, Schur by
a `k`-colour triangle theorem giving `R_k(3) ≤ 3·k!`, and `R(3,k)` by reusing Ramsey's off-diagonal Erdős–Szekeres induction. Cap set, Roth and
Ruzsa–Szemerédi are total by construction, and so are the three graph problems, suprema over a
`Fintype` of graphs. `ex(Qₙ, C₄)` ranges over subgraphs of the hypercube, which Mathlib does not
define at the pin, so `HypercubeC4` defines it.

The Roth and Ruzsa–Szemerédi lower seeds are deliberately weak. Their Mathlib lower bounds
go through Behrend's construction over `ℝ`, which is noncomputable and so cannot be a record; the
first real submissions are the base-3 construction for Roth (`≈ n^{0.63}`) and disjoint
triangles for Ruzsa–Szemerédi (`⌊n/3⌋`). The three graph problems, admitted 2026-09-21, have
trivial seeds in both directions.

## Adding a problem

[`docs/ADDING_A_PROBLEM.md`](docs/ADDING_A_PROBLEM.md) lists the files a new problem must
provide. A problem is admitted only if no closed form for `f` is known and none is expected soon.

## Core concepts

- **`BoundFn`** — just `ℕ → ℕ`. There is no expression DSL; a bound is an ordinary Lean
  function, so anything you can define and prove is admissible.
- **The record** — the current best verified bound for a problem, in one direction.
  Append-only and versioned; each version is a Lean definition plus its proofs, judged
  against a Challenge frozen for that version, so it can be re-verified at any time.
- **The three obligations** — `valid` (it bounds `f`), `improves` (it regresses nowhere),
  `strict` (it beats the record at some `n₀ ≥ nMin`). Only `valid` is ever hard.
- **The two idioms** — `patch` overrides the record at a point; `maxWith`/`minWith` folds
  in an unrelated bound. Both make `improves` a one-liner, so it is never a barrier to
  contributing.

## Project layout

```
SqueezeBench/                       -- this Lean project
├── lean-toolchain                  -- leanprover/lean4:v4.31.0
├── lakefile.toml                   -- pins Mathlib v4.31.0
├── docs/                           -- DESIGN (the specification), CONTRIBUTING, PIPELINE, COMPARATOR, ADDING_A_PROBLEM
├── evaluation/                     -- the baseline protocol: prompt template, runner, and each run's report
├── SqueezeBench.lean               -- root aggregator
├── SqueezeBench/
│   ├── Core.lean
│   ├── Core/
│   │   ├── Bound.lean              -- BoundFn, bound predicates, improvement relations
│   │   ├── Record.lean             -- patch / maxWith / minWith + obligation lemmas
│   │   └── Admissible.lean         -- admissibility gate checks
│   ├── Tool/                       -- `lake exe squeeze`: new / verify / audit / test / accept / bootstrap
│   └── Problems/<Problem>/         -- Def.lean, Finite.lean where well-posedness needs one, README.md, Records/<Dir>/V<k>/
├── Challenges/<Problem>/           -- the trusted statement of record, one per version and
│                                      direction, with its comparator config; problem.toml
├── Fixtures/                       -- nine fixtures: records that must be rejected, turned away or
│                                      accepted, one per gate and two for native evaluation;
│                                      checked by `squeeze test`
├── scripts/
│   ├── bootstrap_tools.sh          -- builds the pinned verifier tools into .tools/ (gitignored)
│   ├── landrun-wrapper.sh          -- the sandbox shim Comparator execs
│   └── tools.lock                  -- pins for landrun and nanoda; Comparator is in lake-manifest.json
└── leaderboard/<problem-id>/       -- NOT YET: record history + ownership regions
```

Everything for one problem — its Lean definition, its proofs, its known values and its
literature — lives in a single directory under `SqueezeBench/Problems/`. Lean files
carry self-contained comments; the design reasoning lives in the Markdown.

[`docs/PIPELINE.md`](docs/PIPELINE.md) walks one submission through the tools. The maintainer tool is `lake exe squeeze`: `new` lays out the next record version, `verify`
runs the admission gates on a record directory, pending or accepted, `audit` runs them on
every accepted record, `test` checks the fixtures, `accept` opens the next Challenge after a
merge, and `bootstrap` builds the verifier tools. It is Lean (`SqueezeBench/Tool/`); the
two shell scripts left are the tool builder and the sandbox shim.

## Building

Requires [`elan`](https://github.com/leanprover/elan) (Lean toolchain manager). Every
command runs from this directory, `SqueezeBench/`, and paths in the docs are relative to it.

```sh
lake exe cache get           # download prebuilt Mathlib (first time)
lake build                   # build the library
lake exe squeeze bootstrap   # only to verify submissions: builds comparator, lean4export, landrun, nanoda (Linux)
```
