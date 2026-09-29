# Golomb, upper record, V008

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V007.record, winLen)` with `winLen m = (m−1)·p`, `p = nextPrime m`
(V002's least prime above `m`). Witness `n₀ = 29`: `929 → 868`. It improves the record at
every `m ≥ 29`: V006's `p(p−1) − 1` becomes `(m−1)p`, a saving of `p(p−m) − 1`, i.e. `p − 1`
just below a prime and much more just above one (`m = 32`: `1331 → 1147`; `m = 100`:
`10099 → 9999`).

**Idea.** Ruzsa's set (V006) is Sidon *modulo* `n = p(p−1)` with `k = p − 1` residues, and a
Sidon set modulo `n` may be rotated freely. Double counting: each residue lies in `L + 1` of
the `n` cyclic windows `[t, t+L]`, so if every window held at most `m − 1` residues we would
have `k(L+1) ≤ (m−1)n`; with `L = ⌊(m−1)n/k⌋` this fails, so some window holds `m` residues,
which after rotation are `m` naturals in `[0, L]`, still Sidon because an equality of sums of
rotated residues is a congruence of the original sums. For Ruzsa `n/k = p`, so `L = (m−1)p`.
This is the standard "a `k`-element Sidon set mod `n` contains `m` elements in an interval of
length `(m−1)n/k`" observation, e.g. in the surveys of O'Bryant (*A complete annotated
bibliography of work related to Sidon sequences*, Electron. J. Combin. DS11, 2004) on
truncating modular constructions.

**Why this before Bose–Chowla/Singer.** The lemma `f_le_of_sidonMod` is generic: it takes any
Sidon set modulo `n` and gives `f m ≤ ⌊(m−1)n/k⌋`, so Bose–Chowla (`p` residues mod `p² − 1`)
and Singer (`p + 1` residues mod `p² + p + 1`) will plug into it directly, with
`⌊(m−1)(p²−1)/p⌋` and `(m−1)p` respectively. Doing the combinatorics once, on the ruler
already in the record, was the shortest path to an improvement at all `m ≥ 29`.

## How the proofs were obtained

By an AI agent (see Setup), by hand-written Lean, no search.

- `window_exists`: Mathlib's pigeonhole `exists_lt_card_fiber_of_mul_lt_card_of_maps_to` on
  the pairs `(x, j) ∈ S × [0, L]` mapped to the rotation `t = (j + n − x) mod n`; the fiber
  over `t` injects into `{x ∈ S : (x + t) mod n ≤ L}` by `Prod.fst`.
- `f_le_of_sidonMod`: rotate by that `t`, take the image in the window, check the three
  hypotheses of V006's `f_le_of_sidon` (Sidon over `ℕ` via `Nat.ModEq.add_right_cancel'`,
  cardinality via injectivity of rotation on residues, bound `< L + 1`).
- `ruzsaRuler_sidonMod`: V006's `ruzsaRuler_sidon` with `Nat.ModEq.of_mul_left/right` in
  place of the integer equality.

Small iterations only: the pigeonhole's hypothesis is stated as `#t * n`, `Set.InjOn` needs
the `Finset` coerced, and an implicit `N` had to be given for `omega` to see `L + 1 − 1 ≤ L`.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. No computation outside Lean.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about 45 minutes.
