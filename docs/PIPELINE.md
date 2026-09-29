# The verification pipeline, in short

This is the overview. The details are in
[`CONTRIBUTING.md`](CONTRIBUTING.md) (what a submitter writes), [`DESIGN.md`](DESIGN.md)
§8 (the gates as specification), and [`COMPARATOR.md`](COMPARATOR.md) (why the judge is
Comparator, and why proofs must be kernel-checked).

## 1. The steps

A submission is a new record version: a directory
`SqueezeBench/Problems/<P>/Records/<Dir>/V<k>/` with `Def.lean` (the bound function),
`Proof.lean` (the three obligations), `metadata.toml` (author and witness) and `REPORT.md`
(how the record was obtained, and the setup used), answering
the open Challenge `Challenges/<P>/<Dir>/V<k>.lean`.

| step | who | command | result |
|---|---|---|---|
| 0 | anyone, once per machine | `lake exe cache get`, `lake build`, `lake exe squeeze bootstrap` | Mathlib cache, the library, and the verifier tools in `.tools/` (Linux only) |
| 1 | submitter | `lake exe squeeze new <P> <lower\|upper>` | the record directory laid out for the open version, statements copied from the Challenge |
| 2 | submitter | edit `Def.lean` and `Proof.lean`; `lake build <module>.Proof` | the record compiles |
| 3 | submitter | `lake exe squeeze verify <record-dir>` | the six gates below pass locally (gate 1 is skipped without `--base`) |
| 4 | submitter | open a pull request that adds only the record directory | |
| 5 | CI or a maintainer | `lake exe squeeze verify <record-dir> --base main` | all six gates, from a fresh checkout |
| 6 | maintainer | merge | acceptance is the merge; nothing in the record is rewritten |
| 7 | maintainer | `lake exe squeeze accept <P> <lower\|upper>` | the next Challenge `V<k+1>` is opened and the problem README updated; commit both |
| 8 | anyone | `lake exe squeeze audit` | every accepted record re-verified against the Challenge that admitted it |
| 9 | anyone | `lake exe squeeze test` | every fixture under `Fixtures/` produces its expected exit code |

## 2. The six gates of `verify`

`lake exe squeeze verify` refuses first, before any gate, a version whose successor Challenge
already exists (exit 3: rebase). Then, in order:

1. **Diff restriction.** The pull request touches nothing outside the record directory.
   Everything else, the Challenges, the core, the configs and the tool pins, is trusted.
2. **Size limits and `Def.lean` restriction.** `Def.lean` is at most 64 KB and the record
   directory at most 1 MB, unless the problem's `problem.toml` sets `max-def-bytes` or
   `max-record-bytes`. The file is parsed, never elaborated: it may import only the
   trusted spine and the predecessor's `Def.lean`, and may contain only plain `def` and
   `abbrev`. This is what keeps later Challenges honest, since they import this file.
3. **Comparator**, unmodified, described below: the statements match the Challenge, the
   axioms are the permitted ones, and two independent kernels accept the proof, within 30
   minutes and 16 GB of memory for the whole run. A proof that
   uses `native_decide`, `bv_decide` or `bv_check` fails here.
4. **Computation budget.** `Proof.lean` is elaborated again, in a read-only sandbox under
   8 GB, with `Elab.async` off so the kernel's work is counted. Each declaration must stay
   within 200000 heartbeats, and so must the whole file. `set_option` is limited to
   `linter.*` and `pp.*`, and metaprogramming commands and code-registering attributes are
   refused, so the file cannot lift the limits (`DESIGN.md` §5.6).
5. **Admissibility.** The record function is computable and its definition does not reach
   the problem's `f` or any other oracle named in `Challenges/<P>/problem.toml`.
6. **Fuel budget.** `decide +kernel` settles the witness comparison against the previous
   record within the problem's heartbeat budget and 8 GB of memory, so the next submitter can
   build on this record. It also evaluates the record, by settling `0 ≤ record n`, at every `n`
   from `nMin` to `fuel-range-max` (default 100), each within the same budget, so a record that
   searches for `f` is rejected. A version after the seed without a witness is rejected.
   Heartbeats count work, not time, so the result is the same on every machine.

Exit codes: 0 accept, 1 reject, 2 the tools or arguments are wrong, 3 rebase needed.

## 3. What each tool does

**`lake exe squeeze`**, the maintainer tool (`SqueezeBench/Tool/`):

- `new` writes the record directory for the open version. It reads the Challenge and
  copies its statements, so the submitter cannot state the wrong thing by accident.
- `verify` runs the rebase check and the six gates on one record or fixture directory.
- `audit` runs `verify --accepted` on every accepted record and prints a summary. The scope
  narrows by position: `audit Golomb`, `audit Golomb upper`, `audit Golomb upper V000` for
  one record against the Challenge that admitted it.
- `test` runs `verify` on every fixture and compares the exit code with the fixture's
  `expect`.
- `accept` opens the next Challenge after a merge and updates the problem README. It never
  edits the record.
- `bootstrap` builds and fetches the external tools below into `.tools/`.

**External tools**, pinned in `lake-manifest.json` and `scripts/tools.lock`:

- **Comparator** (leanprover/comparator), the judge of gate 3, run as released. It builds
  the Challenge and the record in sandboxes, exports both as kernel terms, checks that the
  record's declarations have exactly the Challenge's types and that everything those types
  mention is identical on both sides, checks that no axiom outside `propext`, `Quot.sound`
  and `Classical.choice` is used, and replays the proof through nanoda and the Lean kernel.
  It can be run by hand on any `V<k>.comparator.json`.
- **lean4export** turns a built module into a text export of kernel terms. Comparator reads
  that, never a `.olean`.
- **nanoda**, an independent re-implementation of Lean's kernel in Rust. Together with the
  Lean kernel this gives two checkers for every proof.
- **Lean4Checker**, used by Comparator: its replay feeds the export to the Lean kernel in a
  fresh environment.
- **landrun** sandboxes every build and export. The record's build can write only under
  `.lake`; `scripts/landrun-wrapper.sh` is the shim Comparator execs.

## 4. What is trusted, in one paragraph

The Lean kernel or nanoda, the Challenge files and the `Def.lean` spine they import,
Mathlib at the pinned revision, the lakefile and the tool pins, landrun, and the maintainer
who reads a Challenge in the commit that creates it. No compiled code is trusted: a proof
that relies on native evaluation is rejected. The submitter is trusted for nothing.
