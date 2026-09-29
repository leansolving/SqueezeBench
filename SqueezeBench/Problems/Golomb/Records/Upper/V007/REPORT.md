# Golomb, upper record, V007

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V006.record, small)` where `small` tabulates the optimal lengths
`f(18) = 216`, `f(19) = 246`, `f(20) = 283`, `f(21) = 333`, `f(22) = 356`, `f(23) = 372`,
`f(24) = 425`, `f(25) = 480`, `f(26) = 492`, `f(27) = 553`, `f(28) = 585` and is the previous
record elsewhere. Witness `n₀ = 28`: `811 → 585`. With this the record is exact at every
`m ≤ 28`, i.e. at every `m` where `f` is known, and can never be improved there again.

**Sources.** OEIS A003022 for the values; the rulers themselves are the optimal rulers of
Wikipedia's *Golomb ruler* table (Shearer 1990 for `m ≤ 16`, Dollas–Rankin–McCracken 1998 for
`m ≤ 19`, distributed.net OGR-20 … OGR-28, 2000–2022). The 28-mark ruler is the 27-mark one
with the mark `585` appended. Each ruler was re-checked in a five-line Python script
(distinct positive differences) before being typed into Lean; the kernel is the judge anyway.

## How the proofs were obtained

By an AI agent (see Setup), by hand-written Lean, no search.

The previous versions checked `IsSidon` on a `Finset` literal by `decide +kernel`, which
quantifies over four marks and costs `≈ m⁴` heartbeats — `m = 16, 17` alone took 146k of the
200k budget, so the table stalled at `m = 17`. This version replaces that by a check that
is quadratic in `m` and reasons about it once:

- `sidonCheck l 0` walks the list, and for each mark `a` inserts the sums `a + b` (`b` at or
  after `a`) into a `Nat` bitset, failing on a repeated sum. `testBit`, `|||` and `<<<` are
  GMP-accelerated in the kernel, so the `m(m+1)/2` insertions are cheap: the 28-mark ruler
  costs about 900 heartbeats, against `28⁴ ≈ 600k` for the old check.
- `rulerCheck l L` adds `l.Nodup`, `L ∈ l` and `∀ x ∈ l, x ≤ L`, all cheap `decide`s.
- `sidonCheck_spec` (by induction on the list, with the bitset abstracted as a `Set ℕ` it
  represents, `Repr`) proves that a passing check gives the Sidon property on the list: the
  head's sums are fresh with respect to everything inserted before, the tail is Sidon by
  induction, and a sum of two tail marks can never be one of the head's sums. The 16-way
  case split (each of the four marks is the head or in the tail) is nine `omega`s, six
  contradictions with that freshness, and the induction hypothesis.
- `f_le_of_rulerCheck` turns the list into the `Finset` and the four `RulerLengths`
  conditions, so each table entry is one `exact … (by decide +kernel)`.

Two iterations. `rcases … with rfl` substituted the wrong variable in the case split, fixed
by naming the equations and rewriting. More surprising: discharging the eleven-way `if` chain
of `small` with `unfold small; split_ifs` cost 175k heartbeats by itself (nested `split`,
85k), which `squeeze verify` measured before acceptance; a chain of `by_cases m = 18; subst`
with the entries as separate theorems `f18`, …, `f28` costs 583. The whole file is 13561
heartbeats, of which the eleven kernel checks are 7100 (440 at `m = 18` to 873 at `m = 28`)
and `sidonCheck_spec` 3162.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. Python 3 only to re-check the rulers' differences before typing them in.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about one hour.
