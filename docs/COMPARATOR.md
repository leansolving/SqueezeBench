# SqueezeBench — Comparator

Every submission, and every accepted record on re-verification, is judged by
[Comparator](https://github.com/leanprover/comparator), unmodified, and every proof must be
checked by the kernel alone. This document explains what Comparator guarantees, what it does
not, and what the rest of `lake exe squeeze verify` adds. `DESIGN.md` §n points into
`DESIGN.md`; a bare §n is a section of this file.

## 1. What Comparator checks

Comparator takes a trusted `Challenge.lean` and an untrusted `Solution.lean`, builds both in
separate `landrun` sandboxes, exports both with `lean4export`, and compares the exports. When it
reports success, four things hold:

1. **The statements match.** Each theorem in `theorem_names` has exactly the Challenge's type,
   and each definition in `definition_names` has the Challenge's name, universes and type. Only
   the *body* of such a definition (a *hole*) may differ.
2. **Everything the statements mention is pinned.** Every other constant reachable from those
   types — for us `f`, `nMin`, the previous version's `record` and everything they unfold to —
   must be identical, body included. A record that redefines or shadows `f` fails here.
3. **The axioms are the permitted ones**: `propext`, `Quot.sound`, `Classical.choice`,
   computed on the export, so `sorryAx` or a native-evaluation axiom (§7) is caught.
4. **The proofs check**, replayed through the Lean kernel and through `nanoda`, an independent
   type checker.

In short: given a trusted Challenge and a clean build, the record proves exactly the
Challenge's statements, about exactly the Challenge's objects, from exactly the permitted
axioms, according to two independent kernels.

Comparator is a Lake dependency pinned in `lake-manifest.json`; `squeeze bootstrap` builds it,
and `squeeze bootstrap` and `squeeze verify` refuse to run unless its toolchain equals ours.

## 2. What it does not check, and what does

| not guaranteed by Comparator | closed by |
|---|---|
| that a hole is filled *meaningfully*: `record := f` proves every obligation | the admissibility gate against `problem.toml`'s `oracles` (`DESIGN.md` §5.2) |
| that the record is computable, or cheap to evaluate | the computability and fuel gates (`DESIGN.md` §5.2) |
| that a proof reasons rather than has the kernel search | the computation budget (`DESIGN.md` §5.6) |
| that the Challenge's imports are honest: earlier records' `Def.lean` files could carry a `macro_rules` or `instance` that changes the statement on both sides | the `Def.lean` gate: plain `def`/`abbrev`, fixed imports, checked by parsing (§6) |
| that the record was not compiled before Comparator built it | a fresh checkout in CI; `verify` never builds the record's library itself |
| that the statement is the *open* one | the rebase check (`DESIGN.md` §4.3) |
| a reasonable size or checking time | the size limits and the 30 min / 16 GB cap (`DESIGN.md` §8) |
| that the pull request changed nothing else | the diff restriction (§5) |
| that `f` formalises the intended problem | a human, once per problem |

## 3. The Challenge: a definition hole

A Challenge declares `record` as a hole and states the obligations against it, following
Comparator's documented pattern. It is one static file per version, written by `squeeze accept`:

```lean
-- Challenges/Tutorial/Lower/V002.lean
import SqueezeBench.Core
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Def

namespace SqueezeBench.Tutorial.Lower.V002

def record : SqueezeBench.BoundFn := sorry

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record := sorry
theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record := sorry
theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record := sorry

end SqueezeBench.Tutorial.Lower.V002
```

```json
{ "challenge_module": "Challenges.Tutorial.Lower.V002",
  "solution_module": "SqueezeBench.Problems.Tutorial.Records.Lower.V002.Proof",
  "theorem_names": ["SqueezeBench.Tutorial.Lower.V002.valid",
                    "SqueezeBench.Tutorial.Lower.V002.improves",
                    "SqueezeBench.Tutorial.Lower.V002.strict"],
  "definition_names": ["SqueezeBench.Tutorial.Lower.V002.record"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true }
```

The submission is the record directory, judged by this config both as a pull request and later
by `squeeze audit`. Comparator matches fully qualified names, so the namespace carries the
version.

## 4. Why admissibility is still needed

Comparator's own documentation says definition-hole solutions must always be checked by an
additional verifier. `def record := f` with `valid := fun n => le_refl _` passes Comparator: the
statement matches, there are no axioms, and the theorem is true. It is merely useless, and only
the admissibility gate rejects it (`Fixtures/Tutorial/RecordIsF`).

## 5. Prerequisites

- **Diff restriction.** Comparator builds Challenge and Solution from the same tree, so a pull
  request must touch nothing outside its record directory. Otherwise it could weaken
  `Core/Bound.lean`, add `f` to `definition_names`, or point the verifier's pins at a fork.
- **Trust assumptions.** The Challenge's imports and the lakefile must be trusted, and the
  Solution must not have been compiled before; hence a fresh checkout in CI. `landrun` needs
  Linux and an unprivileged user.
- **Runner.** `scripts/landrun-wrapper.sh` restores the `--` that `landrun` would swallow and
  refuses `--unrestricted-*` flags; everything runs under
  `systemd-run --property=RestrictAddressFamilies=~AF_UNIX`; and the verifier binaries live in
  `.tools/bin/`, outside the sandbox-writable `.lake/`, so a Solution cannot overwrite them.
- **Verbatim types.** A record must copy the declared type exactly: `def record : BoundFn` and
  `def record : ℕ → ℕ` are different to Comparator.

## 6. The trusted base

Each Challenge imports the previous version's `Def.lean`, and through it every earlier one, so
those files are part of what is trusted. That is why records split into `Def.lean` (the
function, imported by the next Challenge) and `Proof.lean` (never imported), and why `Def.lean`
may hold only plain `def` and `abbrev` with a fixed import list (`DESIGN.md` §5.5;
`Fixtures/Tutorial/MacroInDef`). A Solution may use anything the pinned lakefile provides:
Mathlib and the packages it pins.

## 7. Native evaluation is not admitted

`native_decide`, `bv_decide` and `bv_check` each add an axiom stating what compiled code
returned, which no kernel can check. That axiom is not in `permitted_axioms`, so Comparator
rejects any record that rests on one, including an LRAT certificate checked by compiled code.
We expect general proofs, and keeping the judge to the unmodified Comparator means nothing is
trusted beyond the two kernels. `Fixtures/Tutorial/BvCheck` and `PlainNativeDecide` test this.

## 8. Fixtures and cost

`lake exe squeeze test` runs `verify` on each fixture and checks its expected exit code:

| fixture | expected |
|---|---|
| `Bob` | accepted |
| `StaleAgainstV001` | rebase: it answers a version already accepted |
| `MacroInDef` | rejected by the `Def.lean` gate |
| `TooLarge` | rejected by the size limit |
| `ShadowedF` | rejected by Comparator: a local `f` changes the statement |
| `RecordIsF` | accepted by Comparator, rejected by admissibility |
| `WrongWitness` | rejected by the fuel gate |
| `SearchUnderAnotherName` | passes every gate up to the fuel check at its witness; rejected by the fuel gate's range check, at `n = 13` |
| `HeartbeatOverride`, `AsyncOverride`, `MetaCommand` | rejected by the computation budget: the file tries to change its limits |
| `SplitSearch` | rejected by the computation budget: every lemma is within its limit, the file is not |
| `BvCheck`, `PlainNativeDecide` | rejected by Comparator's axiom check |

A full `verify` run on a small record takes under a minute and peaks at about 6.7 GB of memory,
most of it Mathlib.

## 9. Sources

[`leanprover/comparator`](https://github.com/leanprover/comparator) ·
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval) ·
[`PalomarSubmission` SECURITY.md](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/SECURITY.md) ·
[`anthropics/formal-math`](https://github.com/anthropics/formal-math) ·
[Lean manual, "Validating a Lean Proof"](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
