# Ramsey — upper track

`f n = R(n, n)`, the diagonal Ramsey number: the least `N` such that every graph on `N`
vertices has a clique of size `n` or a clique of size `n` in its complement. `nMin = 2`.

## Literature

Exact values (Radziszowski, *Small Ramsey Numbers*, dynamic survey DS1):

| n | R(n,n) |
|---|---|
| 2 | 2 |
| 3 | 6 (Greenwood–Gleason 1955) |
| 4 | 18 (Greenwood–Gleason 1955) |
| 5 | 43 ≤ R(5,5) ≤ 46 (upper bound Angeltveit–McKay, arXiv:2409.15709) |

Relevant off-diagonal values: `R(3,4) = 9`, `R(3,5) = 14`, `R(3,6) = 18`, `R(3,7) = 23`,
`R(4,5) = 25` (McKay–Radziszowski 1995). All of these rest on large computer searches
and are therefore out of reach of the computation budget here.

General bounds, in increasing order of difficulty:

1. **Erdős–Szekeres 1935**: `R(s,t) ≤ R(s-1,t) + R(s,t-1)`, hence
   `R(n,n) ≤ C(2n-2, n-1) ~ 4ⁿ / (4√(πn))`. This is the seed record V000.
2. **The parity refinement**, also in Erdős–Szekeres and standard since:
   `R(s,t) ≤ R(s-1,t) + R(s,t-1) - 1` whenever `R(s-1,t)` and `R(s,t-1)` are both even.
   Proof: on `R(s-1,t) + R(s,t-1) - 1` vertices a counterexample would have to be
   `(R(s-1,t)-1)`-regular, an odd degree on an odd number of vertices, contradicting the
   handshake lemma. This is V001.
3. **Thomason 1988**: `R(n,n) ≤ n^(-1/2+c/√(log n)) · C(2n-2,n-1)`, a polynomial-factor
   saving; needs a quasirandomness development Mathlib does not have.
4. **Conlon 2009**: super-polynomial saving `C(2n-2,n-1) · n^(-c log n / log log n)`.
5. **Campos–Griffiths–Morris–Sahasrabudhe 2023** (arXiv:2303.09521):
   `R(n,n) ≤ (4-ε)ⁿ` with `ε = 2^(-7)`, the first exponential improvement; far beyond
   what can be formalised here in the time available.

## V001 — baseline claude-opus-5

**Bound.** Let `r(s,t)` be the table defined by `r(1,t) = r(s,1) = 1`, `r(s,0) = r(0,t) = 0`
and

```
r(s+1,t+1) = if r(s,t+1) and r(s+1,t) are both even
             then r(s,t+1) + r(s+1,t) - 1
             else r(s,t+1) + r(s+1,t)
```

The record is `record n = r(n,n)`.

**Idea.** The Erdős–Szekeres recursion with the parity saving, run over the whole
off-diagonal table rather than applied once. The new mathematical ingredient is
`forcesOn_step_parity` in `Proof.lean`:

> if `M` and `N` are even, `1 ≤ M + N`, and `M` vertices force `(s, t+1)` while `N`
> vertices force `(s+1, t)`, then `M + N - 1` vertices force `(s+1, t+1)`.

On a vertex set of more than `M + N - 1` vertices the plain step `forcesOn_step` from
`Problems/Ramsey/Finite.lean` already applies. On exactly `M + N - 1` vertices, a graph
with no vertex of degree `≥ M` and no vertex of codegree `≥ N` must satisfy
`deg v ≤ M-1`, `deg_{Gᶜ} v ≤ N-1` and `deg v + deg_{Gᶜ} v = M + N - 2`, so every degree is
exactly `M - 1`. That is odd, on `M + N - 1` (odd) vertices, so `∑ deg v` is odd — but it
equals `2·|E(G)|`. Contradiction. No search anywhere: 16071 heartbeats for the whole file.

**Representation.** `Def.lean` stores the table by *antidiagonals*: `dRow k i` is the entry
at `R(i, k+2-i)`, and the recursion is exactly Pascal's rule with `stepVal` in place of
addition, so it is a plain structural recursion on `k`. Natural subtraction keeps the
right-hand boundary at `0` on its own (`stepVal 0 0 = 0`). `record n = dRow (2n-2) n`.

**Why this bound.** It improves the seed at *every* `n ≥ 4`, by a factor that settles
around `0.88`, and it is exact where the truth is known and reachable: `r(3,4) = 9 = R(3,4)`,
`r(3,5) = 14 = R(3,5)`, `r(4,4) = 18 = R(4,4)`. It needs no search, only the handshake
lemma, so it sits comfortably inside the computation budget.

**Obligations.** `improves` is `dRow k i ≤ C(k, i-1)` by induction on `k`: `stepVal a b ≤ a+b`
and Pascal's rule. `valid` is `dRow_forces`, the entry-by-entry statement that `dRow k i`
forces `(i, k+2-i)`, proved by induction on `k` with a positivity side lemma `dRow_pos`
(needed because the `-1` is only legitimate when the sum is positive).

**Witness.** `n₀ = 5`: `70 → 62`.

## V002 — trial claude-fable

**Status.** Accepted 2026-09-25 (`squeeze verify` ACCEPT, then `squeeze accept`); V003 is the
open Challenge. No work on V003 was started: the session was closed by the maintainers right
after the acceptance, so there is no unfinished version directory.

**Bound.** The V001 table sharpened at every interior entry by a counting bound. Write
`r(s,t)` for the table entry, `A = r(s, t+2)`, `C = r(s+2, t)` and
`es = stepVal(r(s+1,t+2), r(s+2,t+1))` (the Erdős–Szekeres value with the parity saving).
Then

```
r(s+2, t+2) = min(es, x + 1)   where x is the least integer with 3x² > 6x(A+C) + (A−C)²,
            i.e. x = A + C + 1 + ⌊√(4(A² + AC + C²)/3)⌋.
```

The record is `record n = r(n,n)`. On the diagonal (`A = C`) the new step is Walker's
inequality `R(k,k) ≤ 4R(k−2,k) + 2`.

**Idea.** Let `G` be a graph on `V = x + 1` vertices with no `K_{s+2}` and no independent
`(t+2)`-set. Two adjacent vertices have fewer than `A` common neighbours (their common
neighbourhood has no `K_s` and no independent `(t+2)`-set), and two non-adjacent vertices have
fewer than `C` common non-neighbours (no `K_{s+2}`, and an independent `t`-set there extends by
both). Counting paths of length two from both ends, `Σ_v deg(v)² = Σ_{u≠v} codeg(u,v)`, and
inclusion–exclusion turns the second bound into `codeg(u,v) ≤ deg u + deg v + C + 1 − V` for
non-adjacent pairs, so

```
3·Σ deg² ≤ (A − C + 3V − 3)·Σ deg − (V − C − 1)·V·(V − 1).
```

By Cauchy–Schwarz `(Σ deg)² ≤ V·Σ deg²`, which is impossible exactly when
`3x² > 6x(A+C) + (A−C)²`. This is equivalent to Goodman's identity for the triangles of `G`
and `Gᶜ` with the two triangle counts bounded by `(A−1)e(G)/3` and `(C−1)e(Gᶜ)/3`.
No search anywhere.

**Sources.** K. Walker, *Dichromatic graphs and Ramsey numbers*, J. Combin. Theory 5 (1968)
238–243, Theorem 1 (the diagonal form; DS1 §2.3(b) lists it as `R(k,k) ≤ 4R(k,k−2) + 2`);
Y. Li, C. C. Rousseau, W. Zang, *An upper bound on Ramsey numbers*, Appl. Math. Lett. 17
(2004) 663–665 (the general form `R(s+2,t+2) ≤ A + C + 2 + 2√((A²+AC+C²)/3)`).
The Huang–Zhang refinement (JCMCC 28 (1998) 347–350, Theorem 3), which keeps the degree bound
`deg ≤ R(s+1,t+2) − 1` and so excludes the roots of the quadratic when they fall outside the
admissible degree range, is *not* included; see below.

**Why this bound.** It closes the target the earlier passes identified: `r(4,5) = 30` (was
`31`), and it improves the record at **every** `n ≥ 5`, by a growing factor:

| n | V001 | V002 | ratio |
|---|---|---|---|
| 5 | 62 | **58** | 0.935 |
| 6 | 222 | **198** | 0.892 |
| 7 | 814 | **690** | 0.848 |
| 8 | 3026 | **2474** | 0.818 |
| 10 | 42942 | **33018** | 0.769 |
| 11 | 163286 | **122314** | 0.749 |
| 20 | 31324547678 | **20614553026** | 0.658 |
| 40 | — | — | 0.510 |
| 100 | — | — | 0.432 |
| 160 | — | — | 0.397 |

Against the binomial `C(2n−2, n−1)` the ratio behaves like `n^(−0.18)` up to `n = 160`
(Python computation, `log(ratio)/log n ≈ −0.182`, stable from `n = 40` on): a polynomial
saving, of a weaker exponent than Thomason's `n^(−1/2)`.

Selected off-diagonal entries (reporting only): `r(4,5) = 30`, `r(4,6) = 49`, `r(4,7) = 75`,
`r(5,5) = 58`, `r(5,6) = 100`, `r(6,6) = 198`, `r(7,7) = 690`; the `s = 3` row is unchanged
(the counting bound is far weaker than Erdős–Szekeres there, since `A = R(1,t) = 1`).

**Representation (`Def.lean`).** The exact minimum `x` is found by Newton's iteration for the
integer square root (`isqrtAux`, started above the root, at most twelve steps), and `walker`
re-checks the criterion `crit` at the value it returns, so the proof depends only on the
check. Two things were needed to keep the fuel gate happy (the kernel must evaluate
`record n` for every `n ≤ 100` in one process under an 8 GB cap, with Mathlib alone taking
6.8 GB):

- `walker` skips the search when `es ≤ 2(A+C) + 1`, since then the counting bound cannot beat
  `es` (about three quarters of the entries at `n = 100`);
- the table is symmetric, `r(s,t) = r(t,s)`, and entries past the middle of an antidiagonal
  are read mirrored (`mir`), which halves the kernel's work. The table is a single-level
  recursion `rows k = (antidiagonal (k+1), antidiagonal k)` with `next` computing the next
  antidiagonal, and `record n = (rows (2n−3)).1 n`.

A first version with a plain two-level recursion `dRow (k+2) i` (as in V001, plus the
counting bound) built and passed every gate except the fuel range: it needed 1.8 GB on top of
Mathlib at `n = 100` and was rejected at `n = 93` on the memory cap. Measured on this machine
(resident set of `lean -M 12000` on a file evaluating `record 100` by `decide +kernel`):
Mathlib alone 6.8 GB, V001 7.05 GB, first V002 8.64 GB, with the skip 7.67 GB, symmetric
7.28 GB. The kernel's cost is per unfolding step, not per arithmetic operation: two hundred
`walker` calls on 190-bit literals cost nothing measurable, while the table costs about
70 KB per entry.

**Obligations.** `valid`: `forcesOn_walker` is the counting argument (`codeg_adj_lt`,
`commonNon_lt`, `codeg_nonadj_eq`, `sum_codeg`, Mathlib's `sq_sum_le_card_mul_sum_sq`, and
the arithmetic lemma `walker_arith`); `crit_mono` makes the criterion monotone in `x` so the
lemma is stated directly as `ForcesOn (x+1) (s+2) (t+2)`. Mirrored reads are handled by
`forcesOn_symm` (pass to the complement) and `mir_forces`; the table by a plain induction on
`k` (`rows_forces`), reusing V001's `forcesOn_step_parity`. `improves` is `rows_le`, which
needs V001's table to be symmetric (`v1_dRow_symm`). `strict`: witness `n₀ = 5`, `62 → 58`.
Budget: about 90 000 heartbeats for the whole file, the counting lemma 36 000.

**Lean pitfalls met** (so nobody repeats them): a `ForcesOn`-valued application elaborated
against an expected `ForcesOn` type (in `have h := ih j`, or nested as an argument) makes the
elaborator consume the implicit binders of `ForcesOn` and fail with a stuck `DecidableEq`
instance; always `intro V _ _` first and then `exact`, and annotate every such `have`.
`by_cases` on a `ForcesOn` goal introduces those binders too (implicit lambda); `split` does
not. `nlinarith` in the arithmetic core cost 240 000 heartbeats; explicit `ring` identities
plus `linarith` cost 12 000.

**Witness.** `n₀ = 5`: `62 → 58`.


## Values

| n | V000 `C(2n-2,n-1)` | V001 | V002 | R(n,n) |
|---|---|---|---|---|
| 2 | 2 | 2 | 2 | 2 |
| 3 | 6 | 6 | 6 | 6 |
| 4 | 20 | **18** | 18 | 18 |
| 5 | 70 | **62** | **58** | 43–46 |
| 6 | 252 | **222** | **198** | ? |
| 7 | 924 | **814** | **690** | ? |
| 8 | 3432 | **3026** | **2474** | ? |
| 10 | 48620 | **42942** | **33018** | ? |
| 11 | 184756 | **163286** | **122314** | ? |

Note that V001 is **exact at every `n` where `R(n,n)` is known**: `2, 6, 18` at `n = 2, 3, 4`.
Any further improvement must therefore happen at `n ≥ 5`, where the record stands at `62`
against `43 ≤ R(5,5) ≤ 46`.

### Sanity check of the table against known off-diagonal values

Reporting only — none of this feeds a theorem. No table entry falls below a known Ramsey
number, and the table is tight on the first five of them.

| (s,t) | R(s,t) | table `r(s,t)` |
|---|---|---|
| (3,3) | 6 | 6 |
| (3,4) | 9 | 9 |
| (3,5) | 14 | 14 |
| (3,6) | 18 | 19 |
| (3,7) | 23 | 26 |
| (3,8) | 28 | 33 |
| (3,9) | 36 | 42 |
| (4,4) | 18 | 18 |
| (4,5) | 25 | 31 |
| (4,6) | 41 | 50 |
| (4,7) | 61 | 75 |

## What the next improvement would take

The parity saving is the last *elementary* sharpening of Erdős–Szekeres I am aware of, and
it is already optimal given only monotonicity: rounding an odd summand up to the next even
number never produces a smaller `stepVal`. Concretely:

- **A second saving of `1`.** On `M + N - 2` vertices the degree argument no longer closes:
  each vertex has deficiency exactly `1`, the degrees split between `M-2` and `M-1`, and the
  handshake lemma is satisfiable. Some extra structural input is needed.
- **Better base rows.** The `s = 3` row of the table is `6, 9, 14, 19, 26, 33, …` against the
  truth `6, 9, 14, 18, 23, 28, …`. Every known improvement there (`R(3,6) = 18`, `R(3,7) = 23`,
  `R(4,5) = 25`) rests on an exhaustive computer search, which the computation budget rules out
  however it is split up. The asymptotic `R(3,t) = Θ(t²/log t)` (Ajtai–Komlós–Szemerédi, Kim)
  would improve the row at infinitely many `t`, but formalising either half is a large project.
- **Thomason / Conlon / CGMS.** The real asymptotic improvements. Thomason needs
  quasirandomness, Conlon needs a book-type embedding argument, CGMS needs the full
  book algorithm; none of the prerequisites are in Mathlib.

### What I tried for a V002, and why it stopped

After V001 I looked for a second improvement and convinced myself none is available by
elementary means. The reasoning, so nobody repeats it:

- **The parity criterion is complete for the one-vertex argument.** On `M + N - 1` vertices
  the extremal graph must be `(M-1)`-regular, and the handshake lemma is violated exactly
  when `M - 1` and `M + N - 1` are both odd — that is, exactly when `M` and `N` are both
  even. Using the complement instead gives the same condition. So no step of the table can
  be sharpened further this way.
- **A second saving of `1` fails.** On `M + N - 2` vertices every vertex has deficiency
  exactly `1`, so degrees split between `M-2` and `M-1`; writing `a` for the number of
  vertices of degree `M-1`, the handshake lemma only says `a` is even, which is satisfiable.
  The complement gives the same condition again.
- **The diagonal is structurally blocked.** `record n = 2·r(n-1,n)` for every `n ≥ 3`,
  because `r(n-1,n)` comes out odd (`9, 31, 111, 407, …`), so the diagonal step itself never
  earns the parity saving. Lowering `record n` therefore means lowering `r(n-1,n)`, and at
  `n = 5` both of its parents, `r(3,5) = 14` and `r(4,4) = 18`, are already the *exact*
  Ramsey numbers. Any improvement at `n = 5` needs a step lemma strictly stronger than
  Erdős–Szekeres + parity applied to exact inputs. `R(4,5) = 25` shows such a lemma exists
  mathematically, but no elementary one is known.
- **Improving the `s = 3` row does not help.** I checked numerically: substituting the true
  `R(3,6) = 18` for the table's `19` changes `r(4,6)` and `r(4,7)` but leaves `r(3,8)`, and
  therefore the entire diagonal, untouched — `record n` is identical for every `n ≤ 25`. The
  `s = 3` row is in any case already at the elementary optimum: `r(3,t) = ⌊(t²+3)/2⌋`, which
  is Kéry's bound.

So the remaining routes are the ones listed above: a search (ruled out by the computation
budget) or one of the hard asymptotic theorems.

Practical notes for whoever comes next:

- `dRow` is a doubly-branching recursion evaluated by the kernel, so `record n` costs about
  `4^(n-1)` reduction steps. That is fine for a witness up to about `n = 8`; for a larger
  witness, rewrite the table so each antidiagonal is computed once (a `List ℕ` and a
  Pascal-style scan) rather than re-deriving entries.
- `Problems/Ramsey/Finite.lean` already gives `forcesOn_step` in the *sharp* form
  `R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t)` with the side condition `1 ≤ M + N`, plus the base
  cases `forcesOn_zero_left/right` and `forcesOn_one_left/right`. Anything phrased as a
  recursion over the off-diagonal table can be built on those directly.

## Second pass on V001 — baseline claude-opus-5 (no V002 submitted)

A second attempt at a V002 was made in a separate short session. **No version was accepted**:
every elementary route re-examined closes, and the two routes that do not close (Thomason,
Conlon, CGMS, or a search-backed exact value) are out of reach of the computation budget and
of the session's time. What follows is only new evidence, so that a third attempt does not
repeat it. Nothing above is retracted; the checks below agree with it.

### The parity criterion is exhaustive — all four parity cases, both deficiencies

Write `M = R(s-1,t)`, `N = R(s,t-1)`, and let `G` be a counterexample on `V` vertices (no
`K_s` in `G`, no `K_t` in `Gᶜ`). Then `deg v ≤ M-1` and `codeg v ≤ N-1` for every `v`, and
`deg v + codeg v = V-1`.

- **Deficiency 0** (`V = M+N-1`): both inequalities are tight, so `G` is exactly
  `(M-1)`-regular. The handshake lemma fails iff `M-1` and `M+N-1` are both odd, i.e. iff
  `M` and `N` are both even. That is precisely `stepVal`; no other parity case gives a
  contradiction. Using `Gᶜ` (which is `(N-1)`-regular) gives the same condition.
- **Deficiency 1** (`V = M+N-2`): degrees lie in `{M-2, M-1}`. Writing `a` for the number of
  vertices of degree `M-1` and `b = V - a`, the handshake lemma in `G` and in `Gᶜ` give the
  *same* single congruence. Worked through all four parities of `(M,N)`, each one admits a
  consistent solution `(a,b)`, so no contradiction arises in any case. A saving of `2` is
  therefore not available from degrees alone, confirming the note above.

### Rounding a summand up to an even value never helps — checked exhaustively

The report above states this; it was verified by exhaustive search over `0 ≤ a,b < 60`, for
all four choices of replacing `a` by `a` or `a+1` and `b` by `b` or `b+1`: **zero** pairs
where rounding lowers `stepVal`. The four outcomes are
`even/even → M+N-1`, `even/odd` and `odd/even → M+N`, `odd/odd → M+N`, so `stepVal` is
already the pointwise minimum over all legitimate roundings.

### Why the diagonal cannot earn the saving, in one line

`stepVal` produces an **even** value only when both parents are odd. The diagonal entries
`r(n,n)` are even for every `n ≥ 3` (`6, 18, 62, 222, 814, 3026, 11358, …`), and `r(n,n)` is
one of the two parents of `r(n,n+1)`; so `r(n,n+1)` is never even, so `r(n+1,n+1)` never
gets the `-1`. This is a fixed point of the recursion, not an accident of small `n`.

### Which off-diagonal entries actually move the diagonal

Each entry `r(s,t)` was lowered by `1` (and `r(t,s)` with it) and the whole diagonal
recomputed. The result is sharp and worth knowing before spending effort anywhere:

| entry lowered by 1 | effect on `record n` |
|---|---|
| `r(n,n)` itself (`62, 222, 814, …`) | improves that single `n` only |
| `r(n-1,n)` (`9, 31, 111, 407, 1513, …`) | improves **every** `n' ≥ n`, and by `3` at `n` |

So the leverage is entirely on the *near-diagonal* entries `r(n-1,n)`, exactly the ones the
parity rule cannot reach (they are the odd ones). Concretely, `r(4,5) = 31 → 30` would give
the diagonal `2, 6, 18, 59, 215, 795, 2967, 11159, 42239, 160735, …` against the present
`2, 6, 18, 62, 222, 814, 3026, 11358, 42942, 163286, …` — an improvement at every `n ≥ 5`
from one entry. `R(4,5) = 25` is true, so `30` is true; it is the *proof* that is missing.
Lowering `r(3,4) = 9` or `r(4,4) = 18` is not available: those are the exact Ramsey numbers.

**This is the single highest-value target on this track: any proof of `ForcesOn 30 4 5`, by
any means inside the budget, improves the record at infinitely many `n`.**

### Two counting refinements that were tried and are too weak

Both use the codegree bound: if `u ~ v` then `N(u) ∩ N(v)` has no `K_{s-2}` and its
complement no `K_t`, so `codeg(u,v) ≤ A - 1` with `A = R(s-2,t)`.

- **Cherry counting.** Summing `|N(u) ∩ N(w)|` over all pairs, splitting into adjacent pairs
  (bound `A-1`) and non-adjacent pairs (bound only `M-1`, since there a `K_{s-1}` suffices),
  and dividing by `V(M-1)/2` collapses to `M - 2 ≤ (A-1) + (N-1)`, i.e. `M ≤ A + N`. That is
  implied by Erdős–Szekeres itself, so it is vacuous.
- **Caro–Wei inside a link.** `G[N(v)]` has `α ≤ t-1` and maximum degree `≤ A-1`, so
  `|N(v)| ≤ A(t-1)`, giving the true theorem `R(s-1,t) ≤ (t-1)·R(s-2,t) + 1`. On the
  diagonal `M/A ≈ (2n-3)/(n-2) ≈ 2` while `t-1 = n-1`, so the constraint is slack by a
  factor of about `n/2` and never bites. The same computation via Turán on the complement of
  the link gives the identical inequality.

The reason both fail is structural: the table is far enough above the truth that every
consistency check it must satisfy is satisfied with room to spare.

### Attempt at `ForcesOn 30 4 5` — where it stops

This was pushed as far as time allowed, since it is the high-value target. A counterexample
`G` on `30` vertices has no `K_4` and `α(G) ≤ 4`; `deg v ≤ R(3,5) - 1 = 13` and
`codeg v ≤ R(4,4) - 1 = 17`, so every degree is `12` or `13`. Two extra facts come cheaply:

- every link `G[N(v)]` is triangle-free with `α ≤ 4`, hence has maximum degree `≤ 4`, so
  **every adjacent pair has codegree `≤ 4`**;
- for `v` of degree `13`, the link is a triangle-free graph on `13` vertices with `α ≤ 4`,
  and the non-neighbourhood of `v` is a `(4,4)`-Ramsey graph on `16` vertices.

The argument then needs uniqueness of the extremal graphs (`C₁₃(1,5)` for the link, the
Paley graph on `17` vertices minus a vertex for the non-neighbourhood). Those uniqueness
statements are exactly the exhaustive searches the computation budget forbids, and the
degree/handshake counting on top of the codegree bound `≤ 4` does not close on its own. That
is where it was left.

### Summary for a third attempt

Ranked by value per unit of effort:

1. `ForcesOn 30 4 5` (i.e. `R(4,5) ≤ 30`) by a search-free argument — improves every `n ≥ 5`.
   Hardest part is replacing the two uniqueness facts above by counting.
2. Any `ForcesOn (r(n-1,n) - 1) (n-1) n` for a single `n` — same cascading shape, larger `n`
   means weaker hypotheses and possibly more slack to exploit.
3. A single-point patch at `r(n,n)` — allowed, but improves one `n` only and the report
   above is right that it is poor value.
4. Thomason / Conlon / CGMS — the only routes to an asymptotic gain, all needing Mathlib
   development (quasirandomness, book embeddings) that is a project in itself.

## Third pass — baseline claude-opus-5 (no V002 submitted)

A third short session (21 minutes) re-attacked V002. **No version was accepted.** The record
therefore stands at V001, `record n = dRow (2n-2) n`. Nothing above is retracted. What follows
is new material only, so a fourth attempt starts further along.

### New: a *link-regularity* lemma, and why it does not close the (4,5) case

The earlier passes stopped at "the argument needs uniqueness of the extremal graphs". One of
those two uniqueness facts is not needed — it can be replaced by a two-line counting argument.

> **Lemma (extremal links are regular).** Let `m = R(s,t)` and suppose `m - 1 = A + B - 2`
> where `A = R(s-1,t)` and `B = R(s,t-1)` (i.e. the step from `A, B` to `m` earned the parity
> saving). Then every graph `L` on `m - 1` vertices with no `K_s` and no independent `t`-set is
> `(A-1)`-regular.
>
> *Proof.* For `u ∈ L`: `deg u ≤ A - 1` (else the link of `u` has a `K_{s-1}` or an independent
> `t`-set) and `codeg u ≤ B - 1` (same on the complement). But `deg u + codeg u = m - 2 = A+B-2`,
> so both are tight. ∎

Instantiated at `s = 3, t = 5` (`A = R(2,5) = 5`, `B = R(3,4) = 9`, `m = 14 = 5+9`): *every*
triangle-free graph on `13` vertices with `α ≤ 4` is `4`-regular. No search, no uniqueness of
`C₁₃(1,5)` — only `R(2,5) = 5` and `R(3,4) = 9`, both already exact in the table.

So in the target configuration (`G` on `30` vertices, no `K_4`, `α ≤ 4`, aiming at
`ForcesOn 30 4 5`): degrees lie in `{12, 13}`, and for every vertex `v` of degree `13` the link
`G[N(v)]` is a `4`-regular triangle-free graph on `13` vertices. Every adjacent pair therefore
has codegree **exactly** `4` when one endpoint has degree `13`.

Where it still stops: writing `a₁ = #{deg-13 vertices in N(v)}`, `a₂ = #{deg-13 in W}` with
`W = V \ N[v]`, `|W| = 16`, the counts are
`e(N(v), W) = 91 + a₁` and `2·e(W) = 101 + a₂ - a₁`,
so the handshake lemma only reproduces `a₁ + a₂` odd, which is already implied by `a` even. The
`4`-regularity of the link is consumed exactly by the `65 = 5·13` term and buys no new
congruence. Closing `(4,5)` needs a constraint on `W` — a `16`-vertex graph with no `K_4` and
`α ≤ 4`, which is two vertices short of extremal for `R(4,4) = 18` and hence has genuine slack.

### New: the diagonal at `V = 2m-1` is deficiency **0**, not 1

Worth recording because it changes where to look. For the diagonal, `M = N = r(n-1,n) = m`, so
`M + N - 1 = 2m - 1`: a counterexample on `2m-1` vertices is forced to be exactly
`(m-1)`-regular by `deg v + codeg v = 2m-2 = (m-1)+(m-1)`. The parity rule misses it only
because `m` is odd. So the diagonal is *already* at the tight configuration — there is no
deficiency-1 slack to exploit at `record n` itself, and the report's earlier conclusion (the
leverage is on `r(n-1,n)`) is confirmed from a second direction.

Relatedly: proving `R(4,5) ≤ 30` would give `R(5,5) ≤ 61` twice over — once through the table
(`stepVal 30 30 = 59`, in fact) and once directly, since a `30`-regular counterexample on `61`
vertices has links on `30` vertices with no `K_4` and no independent `5`-set.

### New: `R(3,6) ≤ 18` is three-quarters provable without search

Table has `r(3,6) = 19`. The deficiency-1 analysis (`M = R(2,6) = 6`, `N = R(3,5) = 14`,
`V = 18`) gives degrees in `{4,5}`. Let `a` be the number of degree-`5` vertices.

- If `a < 18`, pick `v` of degree `4`. Its non-neighbourhood `H` has `13` vertices, is
  triangle-free with `α ≤ 4`, hence is `4`-regular by the lemma above. Then every `u ∈ H` has
  `e(u, N(v)) = deg_G u - 4 ∈ {0,1}`, so `e(N(v), H) = #{deg-5 vertices of H}`; on the other side
  `e(N(v), H) = Σ_{u ∈ N(v)} (deg u - 1) = 12 + a_N` with `a_N = #{deg-5 in N(v)}`. Hence
  `a = 12 + 2·a_N` and `a_N ≤ 1`.
  - `a = 12` (`a_N = 0`): every degree-`4` vertex has only degree-`4` neighbours, so the six
    degree-`4` vertices induce a `4`-regular triangle-free graph — impossible, a triangle-free
    graph of maximum degree `Δ` has at least `2Δ = 8` vertices (take an edge; the two
    neighbourhoods are disjoint).
  - `a = 14` (`a_N = 1`): the four degree-`4` vertices each have three degree-`4` neighbours, so
    they induce `K₄`, which has a triangle. Contradiction.
- If `a = 18`, `G` is `5`-regular. **This case is open.** Counting gives, for any `v`,
  `e(H) = 20` on the `12`-vertex non-neighbourhood with `H`-degrees in `{3,4}` and exactly four
  of degree `4` — entirely consistent. No contradiction was found.

So the missing step is exactly: *there is no `5`-regular triangle-free graph on `18` vertices
with `α ≤ 5`.* Note, however, that even if this were closed it is **not worth submitting on its
own**: the earlier pass already verified numerically that replacing `19` by `18` leaves
`record n` unchanged for every `n ≤ 25`. It is recorded here because the same
degree-partition technique (`a = c + 2·a_N`, then a structural contradiction on the minority
degree class) is the most promising generic tool found so far, and `(4,5)` is where it should
be aimed next.

### Ranked plan for a fourth attempt

1. `ForcesOn 30 4 5`. Use the link-regularity lemma (now proved, and cheap in Lean: it is the
   `deg + codeg` identity plus the two Ramsey bounds already in the table) to get codegree
   exactly `4` on edges at degree-`13` vertices, then attack `W` — the `16`-vertex graph with no
   `K_4` and `α ≤ 4` — with the degree-partition technique above rather than with handshake
   alone. This improves `record n` at **every** `n ≥ 5`.
2. The `5`-regular case of `R(3,6) ≤ 18`, as a rehearsal of the same technique on a smaller
   configuration; not submittable by itself.
3. Thomason / Conlon / CGMS — unchanged, still out of reach.

Implementation note for whoever writes the Lean: `forcesOn_step_parity` in
`Records/Upper/V001/Proof.lean` is the model to copy. The `deg v + codeg v = V - 1` identity is
`split_card` from `Problems/Ramsey/Finite.lean`, and `SimpleGraph.sum_degrees_eq_twice_card_edges`
is the handshake lemma; both were enough for V001 and both are cheap. Budget was never the
binding constraint on this track — V001's whole file is 16071 heartbeats out of 200000. The
binding constraint is mathematics.

## What the next improvement would take (after V002)

Ranked by value per unit of effort, with what is already in place:

1. **Degree-range refinement (Huang–Zhang 1998).** In the counting argument the degrees of a
   counterexample on `V` vertices lie in `[V − Q, P − 1]` with `P = r(s+1,t+2)`,
   `Q = r(s+2,t+1)` (both parents of the entry, so available in the recursion). The quadratic
   `q(D) = 3D² − (A + 3x − C)·V·D + V²·x·(x − C)` in `D = Σ deg` must then be `≤ 0` for some
   `D ∈ [V(V−Q), V(P−1)]`, not merely for some real `D`. A certificate is: the discriminant is
   negative (V002), **or** `q(V(P−1)) > 0` and `6·V(P−1) ≤ (A + 3x − C)·V` (the parabola is
   decreasing on the range), **or** the mirror image at the lower end. Measured in Python
   (`counting_ok` in the scratch scripts): `r(4,6) = 48`, `r(4,7) = 71`, `r(5,7) = 167`,
   `r(6,6) = 194`, `r(7,7) = 670`, `r(11,11) = 113118` — about 2 % at `n = 6` and 7.5 % at
   `n = 11`. The certificate is not monotone in `V`, so the step lemma needs the reduction
   "no counterexample on exactly `V` vertices ⇒ `ForcesOn V`" (induce on a `V`-subset, with
   `Finset.exists_subset_card_eq`); the degree bounds are the two clique-extension arguments
   already in `forcesOn_walker`, and the parabola argument is
   `q(D) − q(hi) = (D − hi)(3(D + hi) − βV) ≥ 0`. The `Def.lean` cost is a few more big-number
   operations per entry, which the memory measurements above say is affordable; a second
   search below the discriminant bound is not (linear scans are out; a bounded binary search
   with a final certificate check is the pattern to use).
2. **Walker's general criterion with edge-extremal bounds** (McKay–Radziszowski 1995,
   Theorem 1): `Σ_j n_j [2E(s+1,t+2,j) + 2E(t+1,s+2,V−1−j) + 3j(V−1−j) − (V−1)(V−2)] ≥ 0`,
   where `E(r,q,m)` is the maximum number of edges of an `(r,q)`-graph on `m` vertices. V002
   uses `E ≤ m·(max degree)/2`; applying the counting bound recursively to the links gives
   another bound on `E`, but a numerical check at `(5,5)`, `V = 57` shows it is weaker there
   than the degree bound, so the gain would be off-diagonal only.
3. **Thomason / Conlon / CGMS** — unchanged; the only routes to a better exponent than the
   `n^(−0.18)` the counting table achieves.

Practical notes: the scratch scripts (`table.py`, `variants.py`, `variants2.py`, `asym.py`,
`count_entries.py`) under the session's scratch directory compute the V001, V002 and
degree-range tables and the asymptotic ratio; `mem_*.lean` there are the memory probes. The
kernel-side pitfalls (elaboration of `ForcesOn`-valued terms, memory of two-level recursions)
are recorded in the V002 section above and in `Records/Upper/V002/REPORT.md`.
