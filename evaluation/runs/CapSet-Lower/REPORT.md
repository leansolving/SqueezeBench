# CapSet — lower bound track

`f n` = largest size of a cap (three-AP-free set) in `F₃ⁿ`. `nMin = 1`.

Submitters: `baseline claude-opus-5` (V001, V002) and `trial claude-fable` (V003 onwards).

Status at the end of the `trial claude-fable` session: `V003` (the Hill 112-cap, growth rate
`112^(1/6) ≈ 2.1955`), `V004` (a dynamic programme over verified caps in dimensions 1–9,
adding 236, 512, 1082) and `V005` (the extended product construction with `I(m, m-1)`: caps
of size `12 m 112^(m-1)` in dimension `6 m`) are accepted. `V006` is open; a version was
started and is **parked** (the two-level extended product construction with Edel's
admissible set `I(10,5)`, growth rate `2.2173`): its `Def.lean` builds, its `Proof.lean` is
the template, the data and measurements are complete. See *V006 — parked* and *What the
next improvement would take*. The earlier notes of
`baseline claude-opus-5` are kept below unchanged; the part about the computation budget
is superseded by the mask method of V003, which checks a cap in time linear in its size.

## Literature

Exact values (OEIS A090245, offset 0 with `a 0 = 1`):

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| f n | 2 | 4 | 9 | 20 | 45 | 112 | 236 | 496 |

`f 6 = 112` is Potechin (*Des. Codes Cryptogr.* 46, 2008); `f 7 = 236` is
Calderbank–Fishburn (1994) for the lower bound and Potechin for the upper;
`f 8 = 496` is Edel–Ferret–Landjev–Storme (*J. Combin. Theory Ser. A* 99, 2002).
Only values up to `n = 2` are machine-checked in this repository; the rest are
reporting only (`docs/DESIGN.md` §2.2).

General lower bounds, all built on the product rule `f (m + n) ≥ f m · f n`
(the Cartesian product of two caps is a cap):

* `f n ≥ 2ⁿ` — the seed record, `{0,1}ⁿ`.
* `f n ≥ c·λⁿ` with `λ = f k ^ (1/k)` for any `k` with a known cap: `9^(1/3) ≈ 2.0801`,
  `20^(1/4) ≈ 2.1147`, `45^(1/5) ≈ 2.1411`, `112^(1/6) ≈ 2.1952`, `496^(1/8) ≈ 2.2140`.
* `f n ≥ 2.2174ⁿ` for infinitely many `n` — Edel, *Extensions of generalized product
  caps*, Des. Codes Cryptogr. 31 (2004), 5–14, from an admissible set in dimension 480.
* `f n ≥ 2.2202ⁿ` — FunSearch, *Nature* **625** (2024), 468–475, from an admissible set
  in `A(24, 17)` of size 237984. This is the best published growth rate.

Upper side, for context: `f n = O(3ⁿ / n^{1+ε})` (Bateman–Katz) and
`f n ≤ 2.7551ⁿ` (Ellenberg–Gijswijt 2017).

The practical obstacle here is not the mathematics of the product rule but the
**computation budget**: a record has to exhibit a concrete cap and check it inside
200000 heartbeats for the whole `Proof.lean`, kernel work included.

## Starting record

`V000` (seed): `pin nMin (fun n => 2 ^ n)`, i.e. `f n ≥ 2ⁿ` from `{0,1}ⁿ`.

## V001 — `baseline claude-opus-5`

Bound (for `n ≥ 1`):

```
record n = max (2ⁿ) (20 ^ (n / 4) · head (n % 4)),   head = [1, 2, 4, 9] at r = 0,1,2,3
```

Growth rate `20^(1/4) ≈ 2.1147` per dimension, an improvement at every `n ≥ 3`
(and at every `n ≥ 4` strictly, `n = 3` matching `9 > 8`).

Idea. Two ingredients.

1. *Product rule.* `f m · f n ≤ f (m + n)`, proved once and for all in `Proof.lean`:
   extract extremal caps `A`, `B` from `addRothNumber_spec`, push them into
   `F₃^(m+n)` along `Fin.appendEquiv`, and observe that `Fin.append` is additive, so
   a three-term progression in the product projects to one in each factor.
2. *Seeds.* Explicit caps of size 9 in `F₃³` and size 20 in `F₃⁴` (both the exact
   values of `f 3`, `f 4`), found by depth-first search over `AG(n,3)` normalised so
   that the cap contains the affine frame `0, e₁, …, e_n`; `ThreeAPFree` and the
   cardinality are then settled by `decide`. `f 1 ≥ 2` and `f 2 ≥ 4` come from `V000`.

A strong induction on `n` (step `n ↦ n − 4`) turns these into
`20 ^ (n/4) · head (n%4) ≤ f n`, and `maxWith` folds it into `V000`.

Witness: `n₀ = 4`, where `16 → 20`.

Cost: 147873 heartbeats of the 200000 budget, of which `f4` (the `decide` on the
20-cap) alone is 126393. This is the reason the next step cannot simply repeat the
same recipe one dimension up: `ThreeAPFree` by `decide` scans `|A|³` ordered triples,
so 45 points in `F₃⁵` would cost roughly ten times the whole budget.

## V002 — `baseline claude-opus-5`

Bound (for `n ≥ 1`):

```
record n = max (V001 n) (45 ^ (n / 5) · head (n % 5)),   head = [1, 2, 4, 9, 20] at r = 0,…,4
```

Growth rate `45^(1/5) ≈ 2.14112` per dimension, up from `20^(1/4) ≈ 2.11474`. It improves
`V001` at every `n ≥ 5` with `n % 5 ∈ {0, 1, 2, 4}` and, from `n = 10` on, at a positive
fraction of all `n`; asymptotically it is a strict improvement by a factor growing like
`(45^(1/5) / 20^(1/4))ⁿ`.

Idea. The only new mathematical content is a **cap of size 45 in `F₃⁵`**, the exact value of
`f 5`. Everything else is inherited from `V001` by import: `f_mul_le` (the product rule) and
`f1`–`f4`, so this file's whole heartbeat budget is free for the new cap. A strong induction
with step `n ↦ n − 5` gives `45 ^ (n/5) · head (n%5) ≤ f n`, and `maxWith` folds it into `V001`.

Finding the cap. The depth-first searches described below all plateau around 35–39. What works
is a **fixed-size tabu search**: keep exactly 45 points, let
`E = Σ_{p ∈ S} #{pairs of S summing to −p}` (three times the number of violating triples),
repeatedly remove a most-conflicted point and re-insert the least-conflicted non-tabu point,
with a random tabu tenure of 5–16 and restarts. Six independent seeds each found a 45-cap
within seconds. Source kept at `.lake/scratch/CapSet-Lower/tabu.c`.

Checking the cap inside the budget. The `O(|A|³)` `decide` on `ThreeAPFree` used by `V001` is
hopeless at 45 points. `V002` uses the **mask-oracle pair test** sketched at the end of the
`V001` notes, and it works exactly as predicted:

```lean
def enc (v : Fin 5 → ZMod 3) : ℕ := (v 0).val + 3 * ((v 1).val + 3 * (…))
def mask : ℕ := <a 243-bit numeral, bit (enc v) set iff v ∈ pts>
def mem (v : Fin 5 → ZMod 3) : Bool := (mask >>> enc v) % 2 == 1

theorem pts_mem  : ∀ v ∈ pts, mem v = true := by decide +kernel
theorem pts_pair : ∀ x ∈ pts, ∀ y ∈ pts, x = y ∨ mem (y + y - x) = false := by decide +kernel
```

From a progression `x + z = y + y` one gets `y + y - x = z` by `abel`; `z ∈ pts` makes
`mem z = true` by `pts_mem`, so the second disjunct of `pts_pair` is impossible and `x = y`.
`Nat.shiftRight` is a GMP primitive in the kernel, so the mask numeral is free, and the test
is `|A|²` pairs instead of `|A|³` triples with a membership scan. `decide +kernel` (not plain
`decide`) is required: plain `decide` hits `maximum recursion depth` on a 45-element list and
`set_option maxRecDepth` is forbidden.

Witness: `n₀ = 5`, where `40 → 45`.

Cost: 90332 heartbeats of the 200000 budget — `pts_pair` 49333, `pts_mem` 30071, `key` 3841,
`cap_card` 3441. So roughly **24 heartbeats per pair** and, oddly, about 670 per point in
`pts_mem`. These two numbers are the budget model for the next version.

## V003 — `trial claude-fable`

Bound (for `n ≥ 1`):

```
record n = max (V002 n) (112 ^ (n / 6) · head (n % 6)),   head = [1, 2, 4, 9, 20, 45]
```

Growth rate `112^(1/6) ≈ 2.1955` per dimension (the best rate available from a single
explicit cap: `236^(1/7) ≈ 2.183`, `512^(1/8) ≈ 2.181`, `1082^(1/9) ≈ 2.174` are all
smaller). Strictly better than V002 at every `n ≥ 6`. Witness `n₀ = 6`, `90 → 112`.

The cap is the Hill cap: the 56-cap of `PG(5,3)` doubled to `{±v}` in `F₃⁶` (Hill 1973/1978;
Potechin 2008 for the upper bound `f 6 = 112`). It was built as a hemisystem of the elliptic
quadric `x₀x₁ + x₂x₃ + x₄² + x₅²`: a 56-subset of the quadric's 112 points meeting each of its
280 lines in exactly two points is a cap; a small depth-first search finds one in seconds
(`.lake/scratch/CapSet-Lower/claude-1051/…/scratchpad/hill.py`, kept for reference).

**The mask method** (the new ingredient, `V003/Proof.lean`, general in the dimension `n`):
points are base-3 codes `c < 3ⁿ`, the cap is a `3ⁿ`-bit membership mask `M`. The reflection
`y ↦ -(x + y)` acts digit-wise as a transposition of the three values on each axis, and on
`M` a transposition of two slices along one axis is three `&&&` with constant slice masks
plus two shifts. So `refl n x M` (`n` such steps) is the mask of `-(x + A)`, and `A` is a cap
iff `M &&& refl n x M = 1 <<< x` for all `x ∈ A`. The kernel does this with GMP: for the
112-cap the whole check is `≈ 900` heartbeats (the file: 60221, mostly the `omega` calls in
the reasoning lemmas). The theorem `threeAPFree_of_mask n codes M hlt hmem hpair` converts
three `decide +kernel` facts (all codes `< 3ⁿ`; each code is in the mask; the reflection
test) into `ThreeAPFree` of the decoded `Finset`; `dec_inj` and `List.IsChain` give the
cardinality. **A later record needs only a code list, a mask and the same three lines.**

## V004 — `trial claude-fable`

Bound (for `n ≥ 1`): `record n = max (V003 n) (best n)`, where `best` is a dynamic programme
over the table of verified caps `(d, s) ∈ {(1,2), (2,4), (3,9), (4,20), (5,45), (6,112),
(7,236), (8,512), (9,1082)}`: `best 0 = 1`, `best k = max_(d,s) s · best (k - d)`. Witness
`n₀ = 8`, `448 → 512`.

New caps, each checked by the mask method (`V004.le_f_of_codes` packages
`V003.threeAPFree_of_mask` plus the cardinality argument):

* `f 7 ≥ 236`: Calderbank–Fishburn (1994), rebuilt as `A₁ × {0} ∪ A₂ × {1} ∪ A₀ × {2}` from
  the extendable collection `(A₀, A₁, A₂)` of sizes `(12, 112, 112)` in `F₃⁶` (Edel 2004;
  Tyrrell 2023, Lemma 2.14 — see *V005* for the definition). It is a cap precisely because
  of the two conditions E1/E2 of an extendable collection.
* `f 8 ≥ 512`: FunSearch (Romera-Paredes et al., Nature 625 (2024)); explicit construction
  `build_512_cap` from the paper's notebook.
* `f 9 ≥ 1082`: FunSearch; the paper's greedy algorithm with its published priority
  function for `n = 9`, re-run here.

Improvement over V003 at every `n ≡ 1, 2, 3 (mod 6)` and at many others by mixed products
(`n = 16`: `512² > 20 · 112²`). The reflection tests cost 1544, 3629 and 8319 heartbeats for
236, 512 and 1082 points; the whole file 43399. Construction scripts:
`.lake/scratch/CapSet-Lower/claude-1051/…/scratchpad/caps789.py` (kept for reference; the
caps are independently re-checked there before being emitted).

The DP is deliberately generic: `V005` and later only add rows to the table (or families
of rows) and reuse `dp_getD` / `foldl_max_le` / `best_le`.

## V005 — `trial claude-fable`

Bound: `record n = max (V004 n) (best n)` with the dynamic programme of V004 extended by the
rows `(6 m, fam m)`, `fam m = m · 12 · 112 ^ (m - 1)`, for every `m ≥ 1`. Improves V004 at
`n = 60` (`112^10 → 120 · 112^9`) and at every `n ≥ 60`; the factor `12 m / 112` is
unbounded. Witness `n₀ = 60`.

The mathematics is the extended product construction of Edel (2004) as formulated by
Tyrrell (Discrete Analysis 2023, Section 2), now formalised in `V005/Proof.lean`, all for an
arbitrary additive group of blocks `G`:

* `IsCap`, `Extendable` (Definition 2.4: three caps with E1 `x + y + z ≠ 0` for
  `x, y ∈ A₀, z ∈ A₁ ∪ A₂` and E2 for `x ∈ A₀, y ∈ A₁, z ∈ A₂`), `Admissible` (Definition 2.5,
  pair and triple conditions with `Good` = the multiset patterns `{0,0,1}, {0,0,2}, {0,1,2}`);
* `isCap_ext` = Lemma 2.7 (`⋃_{s ∈ S} A_{s₁} × ⋯ × A_{s_m}` is a cap), `card_ext` = the size
  (the pieces are disjoint in characteristic 3);
* `IsCap.map` (caps transfer along injective additive maps), `flatHom` (the flattening
  `(Fin m → Fin d → ZMod 3) →+ (Fin (m d) → ZMod 3)`), `card_le_f` (`IsCap` → `ThreeAPFree`
  → `f`);
* the collection `(A₀, A₁, A₂)` of sizes `(12, 112, 112)` of Lemma 2.14 (`A₀` = weight-1
  vectors, `A₁ = D ∪ R`, `A₂ = D' ∪ R` from the 2-(6,3,2) design
  `{123,124,135,146,156,236,245,256,345,346}`; the third row of the incidence matrix printed
  in the paper is wrong, the block list is right), verified by masks: three cap tests and
  the identities `mask₁ &&& refl 6 x mask₀ = 0`, `mask₂ &&& refl 6 x mask₀ = 0`,
  `mask₂ &&& refl 6 x mask₁ = 0` for the twelve `x ∈ A₀` (`no_sum_of_mask`);
* `Sm m = I(m, m-1)` (`tri m r`: zero at `r`, ones before, twos after), `Sm_admissible`,
  `card_ext_Sm`, `fam_le : fam m ≤ f (m * 6)`.

Cost: 44204 heartbeats, mostly `Extendable.e2'` (the six orders of E2 by `fin_cases`).

## V006 — parked (`trial claude-fable`; not submitted)

Directory `SqueezeBench/Problems/CapSet/Records/Lower/V006/` (`Def.lean` builds, `Proof.lean` is
the template with three `sorry`, `metadata.toml` says witness 192, `REPORT.md` describes the
state). Working files in `.lake/scratch/CapSet-Lower/v006-parked/` (anonymous copies of the
session scratchpad): the Python constructions and checks (`hill.py`, `caps789.py`,
`adm10.py`, `admsearch.py`), the data (`hill112.txt`, `cap7_236.txt`, `cap8_512.txt`,
`cap9.txt`, `coll6.txt`, `adm42.txt`, `adm63.txt`, `adm84.txt`, `adm10.txt`, `orbtab.txt`;
each file: a line of base-3 codes, a line with the membership mask, and for the admissible
sets a line of vectors / representatives), and the Lean prototypes (`Proto.lean` the first
mask test, `P6.lean` the `I(10,5)` admissibility checks, `W6.lean` the witness-cost test).

**The mathematics** (Tyrrell 2023, Definition 2.8 and Lemma 2.9; the FunSearch paper's
"b₀ = a₀·m·a₁^(m-1), b₁ = a₁^m"): a set `S ⊆ {0,1,2}^m` is *recursively admissible* if it is
admissible and any two distinct `s, t` either have coordinates `i, j` with `{sᵢ, tᵢ} = {0,1}`
and `{sⱼ, tⱼ} = {0,2}`, or a common zero. If `(A₀, A₁, A₂)` is extendable in `G` and `S` is
recursively admissible then `(⋃_{s∈S} s(A), A₁^m, A₂^m)` is extendable in `Gᵐ` (proof: new E1
uses a common zero of the two labels and old E1, or the `{0,1}` / `{0,2}` coordinate and old
E2 depending on whether the third point is in `A₁^m` or `A₂^m`; new E2 uses a zero of the
label). `I(m, m-1)` (V005's `tri`) is recursively admissible: for `r < r'` coordinate `r`
carries `(0,1)` and coordinate `r'` carries `(2,0)`. With `m = 8` this gives a collection
`(B₀, B₁, B₂)` of sizes `(fam 8, 112⁸, 112⁸) = (96·112⁷, 112⁸, 112⁸)` in `F₃⁴⁸` (transfer it
along `flatHom 8 6` with an `Extendable.map` lemma, the analogue of `IsCap.map`). Lemma 2.7
with a second admissible set of `|S|` vectors of weight `w` in `{0,1,2}^m` then gives a cap
of size `|S| · (fam 8)^(m-w) · (112⁸)^w` in dimension `48 m`. Rows found and checked in
Python (all independently verified there):

| `S` | `|S|` | dimension | size / 112^(dim/6) | V005 at that `n` | rate |
|---|---|---|---|---|---|
| `I(4,2)`, full | 6 | 192 | 4.41 | 3.43 | 2.2125 |
| `I(6,3)`, full | 20 | 288 | 12.6 | 6.61 | 2.2149 |
| Edel's cyclic `I(10,5)` (26 orbits of the 10-cycle; from *Extensions of generalized product caps*, transcribed via GPT and re-checked: 0 pair and 0 triple violations) | 252 | 480 | 116.6 | 23.3 | **2.2173** |

`I(8,4)` was only found partially (69 of 70) in four minutes of backtracking; not needed.

**Two measured obstacles, and the decisions taken:**

1. *The witness cannot be at 480.* `decide +kernel` on `V005.record 480` alone costs 198286
   heartbeats (`W6.lean`): V005's family fold does one `getD` walk per `m`, i.e. `O(k²)` per
   step and `O(n³)` in all. The witness comparison at 480 costs 423862. So the witness has to
   be `n₀ = 192` (row `I(4,2)`; about 15000 heartbeats for both records), and the 480-row is
   carried for the asymptotics only. V006's own `step` should walk the list once with stride
   6 for the family (structural recursion on the pattern `b :: _ :: _ :: _ :: _ :: _ :: l`, with
   a `famWalk_le` lemma in the style of `foldl_le`), so that later versions stay cheap at
   large `n`. `Def.lean` as parked still has V005's `step` and only the 480-row: change both.
2. *The triple condition of `I(10,5)` over all 31626 pairs costs 188334 heartbeats* (`P6.lean`,
   first version), too much. With the cyclic symmetry it is checked only for pairs
   (representative, any): 26 × 252 pairs, 34649 heartbeats. Checks in `P6.lean` (all pass):
   `codes10 := orbtab.map Prod.fst` (252 codes, increasing), `orb_ok : ∀ (c, r, a) ∈ orbtab,
   r ∈ reps ∧ a < 10 ∧ rot^[a] r = c` with `rot c = c / 3 + c % 3 · 3⁹` (2210), the closure
   `rot c ∈ codes10` (13571 by list search — cheaper: define `mask10 := mkMask codes10`
   with `mkMask l = l.foldl (fun m c => m ||| 1 <<< c) 0` and the lemma
   `(mkMask l).testBit c = true ↔ c ∈ l`, then test the bit), zero counts
   `(univ.filter fun j : Fin 10 => dg j c = 0).card = 5` (2083), the pair condition
   `mask10 &&& zmaskUpTo 10 s 10 = 1 <<< s` (1344), the triple condition
   `∀ r ∈ reps, ∀ t ∈ codes10, r = t ∨ mask10 &&& boxUpTo 10 r t 10 = 0` (34649). Here
   `boxUpTo n s t k = ⋀_{i<k} amask n i (dg i s) (dg i t)` and `amask n i a b` is the mask of
   the third digits `v` for which `(a, b, v)` is *not* a good pattern: `{0}` for `(0,0)`,
   `{b}` for `(0,b)`, `{a}` for `(a,0)`, everything for `(1,1)`, `(2,2)`, `{1,2}` for `(1,2)`,
   `(2,1)` (all masks are closed terms `S n i <<< (v · 3ⁱ)`, so the kernel caches them).

**Proof plan for the symmetry step** (not yet written): `dg k (rot c) = dg ((k+1) % 10) c` for
`k < 10`, `c < 3¹⁰` (from `dg_add_of_lt'`, `dg_succ`, `Nat.add_mul_div_right`), iterated
to `dg k (rot^[b] c) = dg ((k + b) % 10) c`, and `rot^[10] c = c` by `eq_of_dg_eq`. Given
distinct `s, t, u ∈ codes10` with `s = rot^[a] r`, set `b = 10 - a`, `t' = rot^[b] t`,
`u' = rot^[b] u` (in `codes10` by closure), `rot^[b] s = r`; the check for `(r, t')` and the
bit `u'` of `mask10 &&& boxUpTo` give `k` with `Good (dg k r) (dg k t') (dg k u')`, i.e. the
pattern at coordinate `(k + b) % 10` of `(s, t, u)`. The bit characterisation
`(boxUpTo n s t k).testBit u = decide (u < 3ⁿ ∧ ∀ i < k, ¬ GoodN (dg i s) (dg i t) (dg i u))`
follows by induction from `testBit_amask`, which needs the plain form of `testBit_S_shift`:
`(S n k <<< (v·3ᵏ)).testBit u = decide (u < 3ⁿ ∧ dg k u = v)` (write `u = u % 3ᵏ + (u / 3ᵏ) 3ᵏ`).
The pair condition is the same with `zmaskUpTo` (`∀ i < k, dg i s = 0 → dg i u = 0`). Then
`decF n c : Fin n → Fin 3 := fun i => ⟨dg i c, dg_lt i c⟩`, `S10 := (codes10.map (decF 10)).toFinset`,
`Admissible S10`, `S10.card = 252` (via `card_of_codes`), and the size of `ext B' S10` is
`∑_{s∈S10} ∏_j |B' (s j)| = 252 · (fam 8)^5 · (112⁸)^5` by `Finset.prod_ite` with the zero
count. Estimated total for `Proof.lean`: about 100000 heartbeats (35000 of them the triple
check), so the rows for `I(4,2)` and `I(6,3)` (15 and 190 pairs, no symmetry needed) fit too.

The small sets can share all of this: for them the triple check is `∀ s t ∈ codes, s = t ∨
mask &&& boxUpTo n s t n = 0` directly.

## Comparison table

| n | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| V000 (start) | 2 | 4 | 8 | 16 | 32 | 64 | 256 | 1024 | 4096 |
| V001 | 2 | 4 | 9 | 20 | 40 | 80 | 400 | 1600 | 8000 |
| V002 | 2 | 4 | 9 | 20 | 45 | 90 | 405 | 2025 | 8100 |
| V003 | 2 | 4 | 9 | 20 | 45 | 112 | 448 | 2240 | 12544 |
| V004 | 2 | 4 | 9 | 20 | 45 | 112 | 512 | 2240 | 12544 |
| V005 | 2 | 4 | 9 | 20 | 45 | 112 | 512 | 2240 | 12544 |
| f n (true) | 2 | 4 | 9 | 20 | 45 | 112 | 496–512* | ≥ 2240 | ≥ 12544 |

(*`f 8 ≥ 512` is now known from FunSearch; the OEIS entry 496 quoted at the top of this
report is the older bound. Also `496^(1/8) ≈ 2.1724`, not `2.2140` as stated in the old
notes above.)

Further columns where the later versions differ:

| n | 7 | 9 | 13 | 16 | 60 | 66 | 96 | 192 (V006 plan) | 480 (V006 plan) |
|---|---|---|---|---|---|---|---|---|---|
| V003 | 224 | 1008 | 25088 | 250880 | 112^10 | 2·112^11 | 112^16 | 112^32 | 112^80 |
| V004 | 236 | 1082 | 26432 | 262144 | 112^10 | 236·112^10 | 512²·112^14 = 1.04·112^16 | 1.09·112^32 | 1.13·112^80 |
| V005 | 236 | 1082 | 26432 | 262144 | 120·112^9 | 132·112^10 | 192·112^15 | 3.43·112^32 | 23.3·112^80 |
| V006 (planned) | = | = | = | = | = | = | = | 4.41·112^32 | 116.6·112^80 |

Growth rates: V002 `2.1411`, V003–V005 `2.1955` (V005 with an unbounded polynomial factor),
V006 planned `2.2173`; best published `2.2202` (FunSearch), upper bound `2.7551`.

(`V001 n = max(2ⁿ, 20^(n/4)·head₄(n%4))`, `V002 n = max(V001 n, 45^(n/5)·head₅(n%5))`. At
`n = 12` the two are close, 8000 against 8100, because 12 is a multiple of 4; the gap widens
at the `n` that are not.)

## What the next improvement would take

### Current state, after V005 (read this first)

1. **Finish V006** as parked above: about 400 lines of Lean, all of it planned, prototyped
   and measured; the only design decisions still open are cosmetic. Expected result: growth
   rate `2.2173` (Edel 2004), improvements at every `n ≥ 192`, witness `n₀ = 192`. Do not
   try a witness at `n ≥ 480`: `V005.record 480` alone costs 198000 heartbeats.
2. **Then a cheaper record for large `n`.** V005's family fold is `O(n³)` in the kernel; any
   version after V006 that wants a witness beyond `≈ 300` needs V006's stride-6 walk *and* a
   cheaper delegation than `maxWith V005.record` (e.g. prove `improves` by hand so the new
   record does not evaluate the old one — the fuel gate still evaluates `V<k-1>.record n₀`,
   so the witness must be where the old record is cheap).
3. **Beyond 2.2173.** Tyrrell's `2.218` needs the full `I(12,7)` of FunSearch (792 vectors,
   symmetric under three independent 3-cycles) or `I(11,7)` (330): the triple check costs
   about 5 heartbeats per pair, so `≈ 20000` pairs is the limit — `I(11,7)` with its 11-cycle
   symmetry (30 orbits × 330 = 9900 pairs) would fit if the set can be found (Tyrrell's
   Table gives its existence). FunSearch's `2.2202` uses a partial `I(24,17)` of 237984
   vectors and is out of reach for kernel checking.
4. **Small `n`.** Better caps in dimensions 10–12 than the products (2240, 5040, 12544) would
   improve `n ≡ 4, 5, 0 (mod 6)`; none is known to us. The mask method verifies a cap in
   time linear in its size (about 8 heartbeats per point in dimension 9), so any explicit cap
   up to a few thousand points is cheap to add to the table of V004.

### Earlier state, after V002 (kept for the record)

`V003` has to beat rate `45^(1/5) = 2.14112`, so it needs a cap of size `≥ 97` in `F₃⁶`
(true value 112), `≥ 207` in `F₃⁷` (true value 236) or `≥ 442` in `F₃⁸` (true value 496).
The mathematics is free — `V001.f_mul_le` and `V001.f1`–`f4`, `V002.f5` are all importable,
and the `head`/strong-induction/`maxWith` skeleton transcribes by changing five numbers
(see `.lake/scratch/CapSet-Lower/gen.py`, a generator that emits a whole `V<k>` from a cap
file). **The binding constraint is the computation budget, not the search.**

Budget arithmetic from the measured `V002` costs (24 heartbeats per pair in `pts_pair`,
≈670 per point in `pts_mem`):

| cap | pairs | projected `pts_pair` | projected `pts_mem` | total vs 200000 |
|---|---|---|---|---|
| 45 in `F₃⁵` (V002) | 2025 | 49333 | 30071 | 90332 ✓ |
| 97 in `F₃⁶` | 9409 | ≈229000 | ≈65000 | ≈300000 ✗ |
| 112 in `F₃⁶` | 12544 | ≈305000 | ≈75000 | ≈390000 ✗ |

So the mask-oracle pair test as written is about **2–3× too slow** for dimension 6. Two ways out,
both untried:

1. *Do the arithmetic in `ℕ`, not in `Fin n → ZMod 3`.* Almost all of the 24 heartbeats per pair
   go into building `y + y - x` as a `Pi` type and then reading its six coordinates back through
   `Pi.sub`, `Pi.add`, `Matrix.cons` and the `ZMod 3` instances; `Nat` division and shifting are
   GMP primitives and cost nothing. Keep the cap as a `List ℕ` of base-3 codes, define the
   "third point" map on codes by an unrolled six-digit expression, run the pair test entirely on
   codes, and transfer to `Fin 6 → ZMod 3` once by a structural lemma
   `dec (third a b) = -(dec a + dec b)` proved by digit arithmetic (**not** by `decide` — that
   would be 729² pairs). This is the recommended route; it should buy the needed factor.
2. *Halve the pairs by `±` symmetry.* If the cap satisfies `A = -A` then `(x, y)` and `(−x, −y)`
   give the same test, so 6272 pairs suffice at `|A| = 112`. Worth only a factor 2, and it needs
   the cap to be symmetric — which the Hill 112-cap is (it is the cone over the 56-cap in
   `PG(5,3)`), but a tabu-search cap is not.

Note the whole-file limit is also 200000, so splitting `pts_pair` into several declarations
does **not** help.

### On finding the cap

`tabu.c` in `.lake/scratch/CapSet-Lower/` finds 45-caps in `F₃⁵` in seconds from six different
seeds. In `F₃⁶` at target 112 it does **not** succeed in five minutes across six seeds — the
112-cap is the unique (up to affine equivalence) rigid Hill cap and local search does not
stumble on it, consistent with the `V001` notes. Intermediate targets (97–106) in `F₃⁶` were
not run to a conclusion. Two warnings for whoever re-uses `tabu.c`:

* the third-point table must be `unsigned short`, not `unsigned char` — `3⁶ = 729 > 255`, and
  the truncation silently produces sets that *look* like caps to the search but are not;
* always re-check a found set independently (`gen.py` does this before emitting any Lean).

If the budget route above works out, the cleanest source for a genuine 112-cap is the algebraic
one: the Hill cap of 56 points in `PG(5,3)` (Hill, *Caps and codes*, Discrete Math. 14 (1976),
111–119), whose cone `{±v}` in `F₃⁶` is the 112-cap.

### Run notes: the second V003 attempt (nothing accepted)

A ten-minute run by `baseline claude-opus-5` starting from `V002`. It produced no accepted
version. What it established, so the next run does not repeat it:

* **Every cached dimension-6 (and dimension-7/8) cap file in `.lake/scratch/CapSet-Lower/`
  is not a cap.** `t112_1.txt`, `t112_2.txt`, `t112_3.txt`, `n112_11.txt`–`n112_14.txt`,
  `t6_100.txt`, `t6_106.txt` all have the right number of distinct points and all fail the
  independent check in `gen.py` (e.g. in `t112_1.txt`, `200202` and `212002` have their third
  collinear point `221102` in the set). `m112_2*.txt`, `t7_*.txt`, `t8_*.txt` are empty.
  These are exactly the `unsigned short` truncation bug the previous notes warned about:
  the files were written before the fix, so **do not feed any of them to `gen.py`** —
  `gen.py`'s assertion does catch them, which is how this was found.
* `gen.py` itself is in good shape: given a *valid* cap file it emits a complete, compiling
  `V<k>/Def.lean` and `V<k>/Proof.lean` (usage:
  `python3 gen.py <capfile> <dim> <size> V<k> V<k-1> <outdir>`), including the `head` table,
  the strong induction, `maxWith`, and the base cases wired to `V001.f1`–`f4` and `V002.f5`.
  Turning a valid 6-dimensional cap into a candidate `V003` is therefore a one-minute job;
  all of the remaining risk is the heartbeat budget (see the projections above).
* A freshly written, correctly typed tabu search (`.lake/scratch/CapSet-Lower/t6.c`,
  `unsigned short third[729][729]`, remove-most-conflicted / insert-least-conflicted with
  random tabu tenure 5–16 and restarts) was run at targets 112, 104, 100 and 97 for ~12 s
  per seed, three seeds each. **None succeeded in that time.** This is only a weak negative:
  12 s per seed is far less than the budget the dimension-5 runs got, and the dimension-5
  caps also took seconds only after the tenure was tuned. The next run should give this
  search minutes, not seconds, and should start at 97 (the smallest size that beats
  `45^(6/5) ≈ 96.36`) rather than at 112.

Recommended order for the next run, given that ten minutes is not much: (1) run `t6.c` at
97 in the background for several minutes while (2) writing and *measuring* the budget
optimisations below on the existing 45-cap, then (3) `gen.py` + build + verify. Do not start
by trusting any cap file on disk; always run it through `gen.py`'s checker first.

### One budget optimisation worth knowing about

`y + y - x` and `x + x - y` are the *same point* over `F₃` (both are `-(x+y)`), so the
relation tested by `pts_pair` is symmetric and `List.Pairwise` can replace the double
`∀ … ∀ …`, halving the pair count (112 points: 6216 pairs instead of 12544). Recovering the
unordered statement needs `List.Pairwise.forall` plus the one-line symmetry lemma
`∀ a b : Fin 6 → ZMod 3, a + a - b = b + b - a` (`funext`, `Pi.add_apply`/`Pi.sub_apply`, then
`∀ u v : ZMod 3, u + u - v = v + v - u` by `decide` — nine cases). That is a factor 2 on the
dominant term; the projections above say a factor 2–3 is what is missing, so this plus the
`ℕ`-code arithmetic of route 1 should be enough. Neither was measured in this run.

### Earlier notes (written with V001, still accurate)

The mathematics is already in place: `f_mul_le` in `V001/Proof.lean` is general, so a
new record is exactly a new seed cap in some dimension `k` with `f k > 20^(k/4)`.
The realistic candidates are `f 5 ≥ 45` (rate 2.1411), `f 6 ≥ 112` (rate 2.1952) and
`f 8 ≥ 496` (rate 2.2140).

Two obstacles, both real:

* **Finding the cap.** Randomised greedy and annealed local search over `AG(5,3)`
  reach only 39 of 45 within a few minutes; the extremal caps in dimensions 5, 6, 8
  are rigid objects (the 45-cap and the 112-cap are unique up to affine equivalence)
  and want either an exact search with the affine-frame normalisation run to
  completion, or the algebraic construction (Pellegrino / Hill caps, the ternary
  Golay code).
* **Checking the cap inside the budget.** `decide` on `ThreeAPFree` is cubic in `|A|`
  and each step compares functions `Fin n → ZMod 3`, which the kernel unfolds through
  `Fintype.decidablePiFintype`. The way out, which needs no transfer lemmas, is a
  *pair* check with an `O(1)` membership oracle:

  ```lean
  -- p is any Bool-valued function; mask is a 3ⁿ-bit numeral
  def enc (v : Fin 5 → ZMod 3) : ℕ := (v 0).val + 3 * ((v 1).val + 3 * (…))
  def p (v : Fin 5 → ZMod 3) : Bool := (mask >>> enc v) % 2 == 1
  ```

  With `hA : ∀ v ∈ A, p v` and `hP : ∀ x ∈ A, ∀ y ∈ A, x = y ∨ ¬ p (y + y - x)`, three-AP
  freeness follows: `x + z = y + y` gives `z = y + y - x ∈ A`, so `p z` holds and `x = y`.
  That is `|A|²` pairs with a shift instead of `|A|³` triples with a scan — about a
  fortyfold saving at `|A| = 45`. `Nat.shiftRight` is a kernel-accelerated GMP
  primitive, so the mask numeral itself is free.

  This oracle scheme was written and tried on a 39-point set in `F₃⁵` (the best this
  run's local search produced) and it elaborates: the pair test and the cardinality
  both go through. One trap to know about: **plain `decide` dies with
  `maximum recursion depth has been reached`** once the list has around forty
  elements, and `set_option maxRecDepth` is not allowed by the computation budget.
  `by decide +kernel` is the way out — the kernel evaluator has no such limit, and
  `decide +kernel` is the same tactic the fuel gate uses.

Note also that a later record inherits `f_mul_le`, `f1`–`f4` from `V001` by import, so
its own 200000 heartbeats are free for the new cap alone. Concretely, a `V002` only has
to add a cap of size `≥ 43` in `F₃⁵` (or `≥ 90` in `F₃⁶`, or `≥ 181` in `F₃⁷`) to beat
`20^(1/4)`; the rest of `V001/Proof.lean` — the `head` table, the strong induction with
step `n ↦ n − k`, `maxWith` for the two mechanical obligations — transcribes unchanged.

### What was tried and did not work, on the search side

* Lexicographic greedy over `AG(n,3)`: returns exactly `{0,1}ⁿ`, i.e. `2ⁿ`.
* Randomised greedy with restarts: 9, 18, 39, 77 in dimensions 3–6.
* Depth-first search normalised so that the cap contains the affine frame
  `0, e₁, …, e_n` (bitmask implementation, remaining-candidates pruning): finds the
  optimal 9 and 20 in dimensions 3 and 4 in seconds, but only reaches 35 of 45 in
  dimension 5 within several minutes — the tree below the frame is still large.
* Annealed local search (insert a random point, delete one point of each conflicting
  pair, accept a worsening move with probability `T`) at six values of `T` in parallel:
  plateaus at 39 of 45, for every `T` tried.

The extremal caps in dimensions 5 and 6 are unique up to affine equivalence and are
rigid; local search does not stumble on them. The next attempt should either run the
frame-normalised DFS to completion in a compiled language, or build the caps
algebraically — Pellegrino's 20-cap and the Hill 56-cap in `PG(5,3)`, which give
`f 5 = 45` and `f 6 = 112`, come from the ternary Golay code.
