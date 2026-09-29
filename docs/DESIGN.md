# SqueezeBench — Design

What the benchmark is and the rules it enforces. How to submit is in
[`CONTRIBUTING.md`](CONTRIBUTING.md), the verification steps in [`PIPELINE.md`](PIPELINE.md),
why the judge is shaped as it is in [`COMPARATOR.md`](COMPARATOR.md), and how to add a problem
in [`ADDING_A_PROBLEM.md`](ADDING_A_PROBLEM.md).

## 1. Purpose

SqueezeBench collects Lean-verified bounds on problems whose answer is a function
`f : ℕ → ℕ` of one parameter, where:

- `f(n)` is intractable in general, and known exactly only for small `n`;
- the literature brackets it by lower and upper bounds `g(n) ≤ f(n) ≤ h(n)`;
- no closed form for `f` is known, and none is expected soon — otherwise the two records could
  meet at every `n` and the problem would saturate.

Each problem carries a **lower** and an **upper record**: a Lean function `ℕ → ℕ` with a
machine-checked proof that it bounds `f`. A submission replaces a record with a function that
is still a bound, is no worse at any `n`, and is strictly better at some `n`. The record only
improves, and every version of it is a theorem. At each `n` the two records bracket the truth;
where they meet, together they prove the exact value.

### 1.1 Non-goals

Multi-parameter or continuous-parameter problems, autoformalization help, and any ranking of
contributors or bounds by a single score.

### 1.2 Why bounds are plain functions

Comparing two bounds over all `n` (`∀ n ≥ N₀, A n ≤ B n`) is undecidable for any expression
language rich enough to be useful. The benchmark never does it: CI only compares two records at
one witness `n₀`, which is ℕ arithmetic, and pointwise non-regression is a proof the submitter
supplies. So a bound is any computable Lean function. One consequence: the benchmark does not
rank asymptotic quality; an improvement at one `n` counts as an improvement.

## 2. Problem schema

```
SqueezeBench/Problems/<Problem>/
├── Def.lean                 -- f, nMin, and the lemmas that turn a witness into a bound
├── Finite.lean              -- the proof that f is well defined, where one is needed (§6.2)
├── README.md                -- statement, known values, literature, records
└── Records/<Lower|Upper>/V<k>/
    ├── Def.lean             -- `record`, the function alone
    ├── Proof.lean           -- `valid`, `improves`, `strict`
    ├── metadata.toml        -- credit and witness
    └── REPORT.md            -- how the record was obtained (§3.3)
```

Version `k` lives in namespace `SqueezeBench.<Problem>.<Direction>.V<k>`. The standing record
is the highest version; the two directions number independently. `Def.lean` and `Proof.lean`
are separate because the next version's Challenge imports `Def.lean` (§5.5).

### 2.1 Def.lean

`f` must have a real definition — a `sorry` in `f` would put `sorryAx` into every proof about
it — and is pinned to `0` below `nMin`, so bounds need no `n ≥ nMin` hypothesis. `f` is
usually noncomputable; nothing in the pipeline evaluates it.

### 2.2 Known values

Each README lists the known values of `f` with their sources. **They are never a source of
theorems**: most rest on large computer searches that cannot be replayed in Lean, and asserting
them as axioms is barred (§5.4). Where `f` is computable at small `n`, values are checked in
`Def.lean` by `decide` instead.

### 2.3 Per-problem configuration

`Challenges/<Problem>/problem.toml` is trusted configuration, protected by the diff restriction
(§8):

```toml
problem        = "Roth"
n-min          = 1
directions     = ["lower", "upper"]
oracles        = ["SqueezeBench.Roth.f", "rothNumberNat", "addRothNumber"]
fuel-budget-heartbeats = 200000
fuel-range-max         = 100      # optional; the default
max-def-bytes          = 65536    # optional; the default
max-record-bytes       = 1048576  # optional; the default
```

`oracles` are the constants a record's definition may not reach (§5.2).

## 3. Submissions

A submission answers a **Challenge**, `Challenges/<Problem>/<Direction>/V<k>.lean`: a trusted
file, written by the tool, that declares `record` as a hole and states the obligations against
the previous version with fully qualified names. The highest Challenge of a direction is the
open one. A submission is the directory `Records/<Direction>/V<k>/`, added by a pull request
and never changed afterwards. Acceptance is the merge, after which `lake exe squeeze accept`
writes the next Challenge.

### 3.1 The three obligations

For a lower record `l'` against the standing record `l` (upper records mirror this):

```lean
theorem valid    : LowerBoundHolds f l'                 -- ∀ n, l' n ≤ f n
theorem improves : ImprovesLower l l'                   -- ∀ n, l n ≤ l' n
theorem strict   : StrictlyImprovesLower nMin l l'      -- ∃ n₀ ≥ nMin, l n₀ < l' n₀
```

`valid` is the mathematics. `improves` is a one-liner with the idioms of §4.2, and `strict` is
usually `decide` at the witness.

### 3.2 metadata.toml

```toml
name     = "Alice Example"   # the public credit
witness  = 29                # the n₀ of `strict`
based-on = ["V000"]          # optional: earlier versions whose code this record reuses
```

### 3.3 REPORT.md

How the bound and its proofs were obtained: the idea and its sources, how the proofs were
found (by hand, with an AI agent, with automation), and the setup: the models and agents used,
if any, the machine (CPU, memory, operating system), the time spent, and any computation that
ran outside Lean. `squeeze new` writes a template. The reviewer reads the report before merging;
no gate checks it. Records accepted before the report was introduced have none.

## 4. The record

### 4.1 Seeding

A new problem starts with a simple, quickly formalised seed `V000` in each direction. The first
records after the seeds come from the baseline evaluation in [`../evaluation/`](../evaluation),
in which AI agents play the submitter under a fixed protocol.

### 4.2 The two idioms

`patch l n₀ y₀` overrides the record at one point; `maxWith l v` (or `minWith u v`) folds in any
other valid bound `v`. Both come with their `improves` proof, so non-regression is never a
barrier to contributing.

### 4.3 Versioning and rebasing

Records and Challenges are append-only. If two submissions answer the same open version, the
first merged wins; `verify` reports the other as needing a rebase (exit code 3), which is a
rename of the directory and of the version numbers in it.

## 5. Admissibility gates

A submission is rejected by any of these, on top of the Challenge's statement check.

### 5.1 Build and forbidden constructs

1. **Build** — it must build against the pinned toolchain and Mathlib.
2. **Forbidden constructs** — no `sorry`, `admit`, new `axiom`, or native evaluation
   (`native_decide`, `bv_decide`, `bv_check`). This is enforced on the exported proofs (§5.4),
   not by searching the text.

### 5.2 The record must stay usable

`record := f` would satisfy `valid` and `improves`, and the next submitter could never evaluate
it. So:

3. **Computability** — the record must be computable.
4. **No oracle** — its definition must not reach `f` or any constant in `oracles`.
5. **Fuel budget** — the kernel must settle the witness comparison `V<k-1>.record n₀ < record n₀`
   (or its mirror) by `decide +kernel` within `fuel-budget-heartbeats` and 8 GB of memory, so
   the next submitter can prove `strict` against this record by computation. It must also
   settle `0 ≤ record n` at every `n` from `nMin` to `fuel-range-max`, each within the same
   budget: the statement is trivial, but settling it evaluates the record. Every version after
   the seed must declare its witness.

A record must be cheap to evaluate at every `n`, not only at its witness. Gates 3 and 4 do not
ensure this: a copy of `f`'s definition under a new name is computable, reaches no oracle, and
can be cheap at a small witness. It is a true bound, but it equals `f`, so no later version can
beat it and the track is closed. The range part of gate 5 rejects it, because an exhaustive
search exceeds the limits at small `n` (a search for the Tutorial's `f` fails at `n = 13`),
while every accepted record passes up to `n = 100`.
A search placed only above `fuel-range-max` needs a case split on `n` in `Def.lean`, and review
rejects it.

### 5.3 Obligations must be genuine

6. **Witness range** — `n₀ ≥ nMin`, enforced by the Challenge's statement.

### 5.4 Axiom hygiene

7. The axioms of all three theorems must lie in `{propext, Classical.choice, Quot.sound}`, so
   every proof is checked by the kernel alone.

### 5.5 Import policy

| file | may import and contain |
|---|---|
| a record's `Def.lean` | Lean, Mathlib, `SqueezeBench.Core`, the problem's `Def`/`Finite`, the previous version's `Def.lean`; only plain `def` and `abbrev` |
| a record's `Proof.lean` | anything in the pinned dependencies, and the previous version's `Proof.lean`; declarations only: no `set_option` beyond `linter.*` and `pp.*`, no metaprogramming command, no attribute that registers code (§5.6) |

The restriction on `Def.lean` exists because every later Challenge imports it: a `macro_rules`,
`notation`, `instance` or attribute there could change what those Challenges mean. It is checked
by parsing, before anything is built.

### 5.6 Proofs reason; computation checks

The benchmark measures reasoning, as in a pen-and-paper proof. A proof may compute, but only
to check data it provides: a construction, a table, the record's values at small `n`. It may
not have the kernel search for what it should argue. `decide +kernel` is kernel-checked, so
trust does not rule it out as it rules out `native_decide`; cost does:

8. **Computation budget** — `Proof.lean` is elaborated command by command with `Elab.async`
   off, so that the kernel's work is counted too. Each declaration must stay within
   200000 heartbeats (Lean's default `maxHeartbeats`), and so must the whole file, summed
   over its declarations, so a search split into many lemmas is caught as well. The file cannot change
   these limits: `set_option` is allowed for `linter.*` and `pp.*` only, and commands and
   attributes that run code at elaboration time (`run_cmd`, `#eval`, `elab`, `macro`,
   `@[tactic]`, …) are refused. Heartbeats count work, not time, so the verdict is the same
   on every machine. They do not bound memory, so the probe also runs under an 8 GB cap.

Both limits are global constants in `SqueezeBench/Tool/Budget.lean`. The total was set from
the first baseline run: of the 40 records whose proofs do not use `decide +kernel`, 39 total
at most 42k heartbeats (the heaviest declaration 34k); the exception, 103k, is itself a small
search by plain `decide`. The kernel searches needed `maxHeartbeats` raised as far as
100000000 for a single declaration. The per-declaration limit is Mathlib's; a limit on the
whole file has no precedent we know of and follows from the principle above. It is 200000
too, about five times the heaviest reasoning proof. Heartbeats bound work, not memory: a
parallel build of a file with many kernel-checked lemmas can hold several GB even within the
budget, which is what the memory caps of Comparator and of the probe are for.

## 6. Problem suite

### 6.1 The problems

Ramsey, Golomb rulers, cap sets, Schur, `R(3,k)`, Roth, Ruzsa–Szemerédi, `ex(n; C₄)`,
`ex(n; {C₃,C₄})` and `ex(Qₙ, C₄)`, each with a lower and an upper record. The
[project README](../README.md) lists the current records.

### 6.2 Well-posedness

A problem defined as a least `N` (`sInf`) needs a proof that such an `N` exists, since Lean's
`sInf` of an empty set is `0`. Ramsey, Golomb, Schur and `R(3,k)` prove it in `Finite.lean`;
the others are maxima over a finite set and need nothing.

## 7. Repository layout

```
SqueezeBench/
├── SqueezeBench/Core/        -- BoundFn, the obligations, patch / maxWith / minWith, admissibility checks
├── SqueezeBench/Problems/    -- one folder per problem (§2)
├── SqueezeBench/Tool/        -- `lake exe squeeze`: new / verify / audit / test / accept / bootstrap
├── Challenges/               -- the trusted statements and problem.toml, one Challenge per version
├── Fixtures/                 -- records that must be accepted or rejected, checked by `squeeze test`
├── docs/                     -- this file and the guides
├── evaluation/               -- the baseline protocol and its runs
└── scripts/                  -- builds the pinned verifier tools into .tools/
```

### 7.1 Where documentation lives

Lean files carry self-contained comments only; design reasoning lives in the Markdown files.

## 8. CI pipeline

`lake exe squeeze verify <record-dir> --base <ref>` runs, after a rebase check:

1. **Diff restriction** — the pull request changes nothing outside the record directory.
2. **Size limits and the `Def.lean` restriction** (§5.5).
3. **Comparator**, unmodified — statements match the Challenge, axioms are permitted, and two
   independent kernels accept the proof; capped at 30 minutes and 16 GB.
4. **Computation budget** — gate 8 of §5.6, sandboxed and capped at 8 GB.
5. **Admissibility** — gates 3–4 of §5.2.
6. **Fuel budget** — gate 5 of §5.2.

`lake exe squeeze audit` re-runs this on every accepted record, and `lake exe squeeze test` on
the fixtures.
