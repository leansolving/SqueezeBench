# Graphs of girth at least five — `ex(n; {C₃, C₄})`

`f(n)` is the largest number of edges in a simple graph on `n` vertices with no triangle and no
4-cycle — equivalently, of girth at least `5`.

**The leading constant is open.** The classical upper bound is `f(n) ≤ (n/2)·√(n−1)`, about
`0.5·n^{3/2}`, from the Moore-type count: for each vertex, its neighbours are pairwise
non-adjacent and have no other common neighbour, so `1 + Σ_{u ~ v} d(u) ≤ n`. The best general
construction is the point–line incidence graph of a projective plane, which is bipartite of
girth 6 and gives about `0.354·n^{3/2} = (1/(2√2))·n^{3/2}`. Erdős conjectured that the lower
constant is the truth, `f(n) ~ (n/2)^{3/2}` — [Erdős problem #573](https://www.erdosproblems.com/573),
still open. Ma–Yang (2025) improved the lower bound by an additive `c·n^{5/4}`, the first gain
since 1976, but the constant is untouched.

`nMin = 1`.

## Known values

**Reporting only. These are never a source of theorems** (`docs/DESIGN.md` §2.2).

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| f(n) | 0 | 1 | 2 | 3 | 5 | 6 | 8 | 10 | 12 | 15 |

| n | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|
| f(n) | 16 | 18 | 21 | 23 | 26 | 28 | 31 | 34 | 38 | 41 |

Exact values are known for `n ≤ 53` (`f(53) = 181`), the deepest proven prefix of any problem
surveyed for this benchmark, and the sequence is strictly
increasing, so every term is an independent fact. Provenance: Garnick–Kwong–Lazebnik 1993 for
`n ≤ 24`, Nieuwejaar 1992 for `n = 25, 26, 27`, Miller–Codish 2017 for `20 ≤ n ≤ 32`,
Backelin 2015 for `40 ≤ n ≤ 49`, and McKay's computer searches for the rest up to `n = 53`.
From `n = 54` only lower bounds are known (`f(54) ≥ 185`).

Three values are attained by Moore graphs, which meet the upper bound `(n/2)√(n−1)` exactly:
the 5-cycle at `n = 5`, the Petersen graph at `n = 10` (`f(10) = 15`), and the
Hoffman–Singleton graph at `n = 50` (`f(50) = 175`). The only other possible Moore degree is
57, whose existence is a famous open problem.

Citation: OEIS A006856. The values for `n ≤ 9` were also re-derived here by exhaustive search
and agree.

## Formalisation status

`f` is the supremum of `#G.edgeFinset` over the graphs `G` on `Fin n` with `5 ≤ G.egirth`,
pinned to `0` below `nMin`.

The condition uses Mathlib's **extended** girth `egirth`, which is `⊤` on an acyclic graph. The
ℕ-valued `girth` is `0` there, so the empty graph would fail the condition and the supremum could
be empty. `f` is noncomputable and total by construction, so there is no `Finite.lean` and no
well-posedness obligation. Because `f` is noncomputable the known values cannot be checked by
`decide`, so they are cited above — except `f(1) = 0` and `f(3) ≤ 2`, which are proved in
`Def.lean`. The matching `2 ≤ f(3)` needs an explicit two-edge graph and is left to a lower record.

`Def.lean` supplies:

| lemma | use |
|---|---|
| `le_f_of_egirth` | a lower record exhibits a graph of girth ≥ 5 and counts its edges |
| `f_le_of_forall_egirth` | an upper record bounds the edges of every such graph |
| `five_le_egirth_iff` | `5 ≤ egirth` ↔ no triangle, and no two distinct vertices with two distinct common neighbours |
| `f_le_choose_two` | the ambient bound `C(n, 2)` |

`five_le_egirth_iff` is the lemma that makes submissions tractable. Mathlib relates `egirth` to
nothing else — it appears nowhere in `Mathlib/Combinatorics` outside its own file — so without it
every submission would reason about walks directly. The proof goes through `le_egirth` in both
directions: a triangle or a pair of common neighbours builds an explicit cycle of length 3 or 4,
and conversely a cycle of length at most 4 is destructured into one of those two configurations.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`, with trivial
bounds.

| direction | record | source |
|---|---|---|
| lower | `0` | the empty graph |
| upper | `C(n, 2)` | `f_le_choose_two` |

## Where the next improvement lies

- **lower.** The star on `n` vertices gives `n − 1` and has girth ≥ 5 — it is triangle-free, and
  two leaves share only the centre. Real improvements are explicit graphs: the Petersen graph at
  `n = 10`, induced subgraphs of Hoffman–Singleton, and in general the incidence graph of a
  projective plane, which is asymptotically the best known.
- **upper.** The trivial bound is `C(n, 2)`. The first real improvement is the Moore count above,
  giving `(n/2)√(n−1)` and dropping the record from order `n²` to order `n^{3/2}`. Nothing
  better is known in general — improving the constant `½` here would settle Erdős #573.

## Current state

| | |
|---|---|
| Well posed | **yes** — total by construction |
| Lower record | `Records/Lower/V011/` — beats V010 at witness `50` (trial claude-fable; based on V008, V010, 2026-09-25) |
| Upper record | `Records/Upper/V006/` — beats V005 at witness `410` (trial claude-fable; based on V001, V002, V003, V004, V005, 2026-09-25) |
| Live | **yes** — both Challenges open at `V001` |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on ExC4/Lower/V001 | 2 | 0 → 1 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001, ExC4/Lower/V006 | 242 | 241 → 1331 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V002 | 20402 | 111804 → 1030301 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V003 | 2036162 | 101999799 → 1027243729 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V004 | 200280098 | 100669885442 → 1002101470343 |
| V006 | 2026-09-24 | baseline claude-opus-5; based on V005 | 549753716738 | 2749766434621192 → 144114363443707903 |
| V007 | 2026-09-24 | baseline claude-opus-5; based on V006 | 8718968605206943442 | 2285620946142342176178116 → 9102332111866754346145142731 |
| V008 | 2026-09-25 | trial claude-fable; based on V006, V007 | 1000 | 6859 → 10868 |
| V009 | 2026-09-25 | trial claude-fable; based on V008 | 100000000000000000000 | 102129916315531214065351311353 → 176776695300000000000000000000 |
| V010 | 2026-09-25 | trial claude-fable; based on V006, V008, V009 | 266 | 1360 → 1596 |
| V011 | 2026-09-25 | trial claude-fable; based on V008, V010 | 50 | 125 → 175 |

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 10 | 45 → 15 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 15 | 28 → 27 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 18 | 37 → 36 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003 | 19 | 40 → 39 |
| V005 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004 | 11 | 17 → 16 |
| V006 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004, V005 | 410 | 4142 → 4132 |
