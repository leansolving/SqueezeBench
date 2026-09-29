# Adding a problem

A problem is admitted only when `f` is genuinely defined (`DESIGN.md` §2.1 — a definitional
`sorry` is barred, since `sorryAx` would propagate into every submission) and both directions
carry a seeded, proved record. `squeeze` does not see a problem until `Challenges/<P>/`
exists.

---

## File manifest

Nine files you write for a problem whose `f` is **total**; ten if `f` is `sInf`-defined.
`lake exe squeeze accept` writes the rest.

```
SqueezeBench/Problems/<P>/
├── Def.lean                            -- f, nMin, transfer lemmas, known-value examples
├── Finite.lean                         -- only if f is sInf-defined and the proof is long
├── README.md                           -- statement, known values, status, records, history
├── Records/Lower/V000/Def.lean         -- `record`, the seed lower bound
├── Records/Lower/V000/Proof.lean       -- `valid`, and the mathematics behind it
├── Records/Lower/V000/metadata.toml    -- name = "SqueezeBench"
├── Records/Lower/V000/REPORT.md        -- how the seed was obtained (DESIGN §3.3)
└── Records/Upper/V000/{Def,Proof}.lean, metadata.toml, REPORT.md

Challenges/<P>/
├── problem.toml                        -- n-min, directions, oracles, fuel budget, size limits
├── Lower/V000.lean, V000.comparator.json   -- written by `squeeze accept`: the seed's statement
├── Lower/V001.lean, V001.comparator.json   -- written by `squeeze accept`: the open Challenge
└── Upper/…                                 -- likewise
```

`<P>` is a **Lean module name component**: capitalised, no hyphens, not a keyword.

Namespaces, exactly: `SqueezeBench.<P>` for `Def.lean` and `Finite.lean`; `SqueezeBench.<P>.<Dir>.V<k>` for
version `k` of the `Lower` or `Upper` record and for its Challenge. Every version declares
`record` and `valid`; every version after the seed also declares `improves` and `strict`.

Nothing needs registering in `SqueezeBench.lean` — it imports only `Core`, and the
`lakefile.toml` globs pick problems up automatically.

---

## 1. `Def.lean` — the contract

```lean
import Mathlib
import SqueezeBench.Core

/-! Self-contained header: what the object is, the OEIS id, and — if `f` reuses a Mathlib
definition — why that definition *is* the intended object. No reference to DESIGN.md. -/

namespace SqueezeBench.<P>

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- <the object>, pinned to `0` below `nMin`. -/
def f (n : ℕ) : ℕ := if n < nMin then 0 else <the real definition>

end SqueezeBench.<P>
```

Three rules, all load-bearing:

- **Pin to `0` below `nMin`.** This makes validity *total* in both directions — a lower bound
  pads with `0` and `0 ≤ 0`; an upper bound is unconstrained since everything is `≥ 0`. Without
  it every record lemma carries an `n ≥ nMin` hypothesis.
- **`f` may be `noncomputable`** (§2.1 expects it usually is). Only the *record* must be
  computable. `CapSet`'s `f` happens to be computable; `Ramsey`'s is not.
- **Supply the transfer lemmas.** These are what make submissions one-liners, and they are the
  real deliverable of this file. One per direction:

```lean
/-- Lower bounds reduce to exhibiting a witness. -/
theorem le_f_of_<witness> {n : ℕ} (hn : nMin ≤ n) (h : <witness condition>) : <size> ≤ f n

/-- Upper bounds reduce to ruling out witnesses of a given size. -/
theorem f_lt_of_forall_not {n k : ℕ} (hn : nMin ≤ n) (h : ∀ ..., ¬ ...) : f n < k
```

For an `sInf`-defined `f`, the pair is instead `f_le_of_<forces>` (via `Nat.sInf_le`) and
`le_f_of_wellPosed` (via `Nat.sInf_mem`, needing `WellPosed`).

**Known values.** Where `f` is computable, check them rather than tabulating them:

```lean
example : f 1 = 2 := by decide
set_option maxRecDepth 100000 in
example : f 2 = 4 := by decide
```

The build then re-verifies them every run and fails loudly if the definition drifts — which a
README table cannot do. This is also the sharpest test that `f` denotes the intended object.
Values out of reach go in the README with citations, never as theorems (§2.2).

## 2. `Finite.lean` — only if `f` is `sInf`-defined

In `Def.lean`, export the obligation as a `Prop`, never a sorried theorem:

```lean
def WellPosed (m : ℕ) : Prop := {N | Forces m N}.Nonempty   -- Ramsey's is {N | Forces N n n}
```

A sorried theorem is a landmine — anything using it inherits `sorryAx` and *looks* proved. A
`Prop` cannot be misused that way. `Finite.lean` then holds the discharge,
`theorem wellPosed (hm : nMin ≤ m) : WellPosed m`; when that proof is short it may stay in
`Def.lean`, as Golomb's does. Until it is discharged **no lower record can be proved**:
`le_f_of_wellPosed` goes through `Nat.sInf_mem`, which needs the set nonempty. The upper
direction does not need it — `Nat.sInf_le` needs only a member, and for these problems
exhibiting a member *is* the upper-bound theorem, which in turn discharges `WellPosed`.

**If `f` is a `Finset.sup` or `Nat.findGreatest`, skip this file entirely.** Cap set, Roth,
Ruzsa–Szemerédi, `ExC4`, `ExGirthFive` and `HypercubeC4` have no `Finite.lean`. This is why maxima are preferred when choosing problems.

## 3. The seed records — `Def` and `Proof` split

The split is not cosmetic. The Challenge of version `V<k+1>` imports `V<k>/Def.lean` to name
the standing record. An import loads every command in the file, and commands such as
`macro_rules`, `notation`, `instance` or an attribute run when the importing file is
elaborated and can change what the Challenge's text means, unseen by Comparator. So
`Def.lean` may hold only plain `def` and `abbrev` (plus doc comments, `open`, `set_option`),
and may import only Lean, Mathlib, `SqueezeBench.Core`, the problem's `Def` and `Finite`;
`squeeze verify` checks this by parsing the file. `Proof.lean` may contain anything.

```lean
-- Records/Lower/V000/Def.lean   (imports Problems/<P>/Def)
namespace SqueezeBench.<P>.Lower.V000
open SqueezeBench
def record : BoundFn := pin nMin (fun n => <the bound>)   -- `pin` only if needed
end SqueezeBench.<P>.Lower.V000

-- Records/Lower/V000/Proof.lean   (imports the Def, and Finite if there is one)
namespace SqueezeBench.<P>.Lower.V000
open SqueezeBench
theorem valid : LowerBoundHolds f record := pin_lowerBoundHolds fun n hn => ...
end SqueezeBench.<P>.Lower.V000

-- Records/Lower/V000/metadata.toml
name    = "SqueezeBench"
```

Seed with a simple bound that is quick to formalise (`DESIGN.md` §4.1) — never from the known
values, which are not theorems.

## 4. `Challenges/<P>/problem.toml` — the trusted configuration

**`oracles` is the field that matters.** It must name `SqueezeBench.<P>.f` and any other constant a
record must not reach; the admissibility gate rejects a record whose *definition* touches
them. It lives beside the Challenges so the diff restriction (`DESIGN.md` §8) protects it: a submitter able
to edit it could switch off the gate that stops a record being defined as `f` itself.

```toml
problem        = "<P>"
n-min          = 1
directions     = ["lower", "upper"]
oracles        = ["SqueezeBench.<P>.f"]
fuel-budget-heartbeats = 200000
```

`fuel-range-max` (default 100) is the largest `n` at which the fuel gate evaluates a new record;
set it lower only if a good record cannot be evaluated up to 100.
`max-def-bytes` (default 65536) and `max-record-bytes` (default 1048576) may be added when a
problem needs other size limits, e.g. a lower bound whose natural witness is a large explicit
table.

## 5. The Challenges — written by the tool

Once both seeds build, open each track:

```sh
lake exe squeeze accept <P> lower
lake exe squeeze accept <P> upper
```

For a track whose seed has no Challenge yet, `accept` writes two pairs of files:
`Challenges/<P>/<Dir>/V000.lean` (the seed's statement, `record` and `valid` only) and
`V001.lean` (the open Challenge, naming `SqueezeBench.<P>.<Dir>.V000.record` as the record to beat),
each with its `.comparator.json`. Read them in the commit: they are the trusted statement
surface, every name fully qualified so no `open` in a record can redirect what `f` or `nMin`
means. They are `sorry`d by construction and `Challenges` is not a default target.

Then check that the seeds pass their own Challenges:

```sh
lake exe squeeze audit <P>
```

## 6. `README.md`

Follow CapSet's headings in order: statement and `nMin`; **Known values** (marked *reporting
only, never a source of theorems*, with the OEIS id and any offset discrepancy called out);
**Formalisation status**; **Seeded records**; **Where the next improvement lies**; and
**Current state** with a `| Lower record | … |` and `| Upper record | … |` row, which
`lake exe squeeze accept` rewrites on each acceptance. The **Record history** table is created by
`accept` on the first accepted version after the seed.

---

## Checklist before opening the PR

- [ ] `f` has a real definition; **no `sorry` anywhere outside `Challenges/`**
- [ ] `f` pinned to `0` below `nMin`; `nMin_eq` marked `@[simp]`
- [ ] both transfer lemmas present and stated in terms a submitter can discharge
- [ ] known values machine-checked where `f` is computable; cited in the README otherwise
- [ ] both directions seeded as `Records/<Dir>/V000/` with `record`, `valid`, a `metadata.toml` and a `REPORT.md`
- [ ] `problem.toml` names `SqueezeBench.<P>.f` in `oracles`; `squeeze accept` run for both directions
- [ ] `lake exe squeeze audit <P>` accepts both seeds
- [ ] no Lean source references `DESIGN.md` —
      `grep -rn "DESIGN.md" --include=*.lean SqueezeBench/ Challenges/` returns nothing
- [ ] `lake build` clean, and `#print axioms` on both `valid` inside
      `{propext, Classical.choice, Quot.sound}` (no `native_decide`, `bv_decide` or
      `bv_check`)
- [ ] `fuel-budget-heartbeats` checked against the seeds' witness comparisons rather than left at the 200000 default
