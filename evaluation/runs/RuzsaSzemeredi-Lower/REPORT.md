# RuzsaSzemeredi — lower bound — report

`f n` is the largest number of **triangles** in a locally linear graph on `n` vertices (every
edge in exactly one triangle). `nMin = 3`.

## What the literature says

* **Ruzsa–Szemerédi (1978)** — the `(6,3)`-problem. `f(n) = n^{2-o(1)}` and `f(n) = o(n²)`; the
  truth in between is open.
  I. Z. Ruzsa, E. Szemerédi, *Triple systems with no six points carrying three triangles*,
  Combinatorics (Keszthely 1976), Colloq. Math. Soc. János Bolyai 18 (1978), 939–945.
* **The construction.** Every lower bound known goes through 3-AP-free sets. From a 3-AP-free
  `A ⊆ [0, m)` one builds a tripartite graph on `Z_{2m+1} ⊕ Z_{2m+1} ⊕ Z_{2m+1}` whose triangle
  indices are `(x, x+a, x+2a)`, `a ∈ A`. It is locally linear and has `(2m+1)·#A` triangles.
  Mathlib has it as `rothNumberNat_le_ruzsaSzemerediNumberNat`:
  `(2m+1) · r₃(m) ≤ ruzsaSzemerediNumberNat (6m+3)`.
* **Szekeres' 3-AP-free set** — the integers below `m` whose base-3 digits avoid `2`. Size
  `m^{log 2 / log 3} = m^{0.6309…}` (exactly `2^⌊log₃ m⌋` at powers of 3). Combined with the
  construction: `f(n) ≫ n^{1.63}`.
* **Behrend (1946)** — `r₃(m) ≥ m·exp(-c√(log m))`, hence `f(n) ≥ n²·exp(-C√(log n))`, i.e.
  `n^{2-o(1)}`. F. A. Behrend, *On sets of integers which contain no three terms in arithmetical
  progression*, Proc. Nat. Acad. Sci. USA 32 (1946), 331–332. Mathlib has this as
  `ruzsaSzemerediNumberNat_lower_bound`, but it is stated over `ℝ` through `Real.exp`/`Real.log`
  and is therefore **not usable as a record** (a record must be computable).
* **Upper side**, for context: `f(n) = n² / e^{Θ(log* n)}` via the triangle removal lemma
  (J. Fox, *A new proof of the graph removal lemma*, Ann. of Math. 174 (2011), 561–579).
* **Small exact values.** No published table and no OEIS entry was found for `f`. The problem
  README reports values computed by SqueezeBench: `f(3..13) = 1,1,2,2,3,4,6,6,7,9,10`.
* **Small exact values of `r₃`** (largest 3-AP-free subset of `[0, m)`, OEIS A003002), recomputed
  here by exhaustive search for `m = 1..45`:
  `1,2,2,3,4,4,4,4,5,5,6,6,7,8,8,8,8,8,8,9,9,9,9,10,10,11,11,11,11,12,12,13,13,13,13,14,14,14,14,15,16,16,16,16,16`.
  An earlier note in this report listed `r₃(11) = 5`; the set `{0,1,3,4,9,10}` shows it is `6`.

* **Cap sets** (added by trial claude-fable). In `F₃^k` a 3-AP `a + c = 2b` is a line
  `a + b + c = 0`, so 3-AP-free sets are *caps*, and caps are far larger than digit sets: the
  maximum affine caps are `2, 4, 9, 20, 45, 112` in dimensions `1..6` (the last is the Hill cap;
  R. Hill, *On the largest size of cap in S₅,₃*, Atti Accad. Naz. Lincei Rend. 54 (1973) 378–384;
  Y. Edel, S. Ferret, I. Landjev, L. Storme, *The classification of the largest caps in
  AG(5,3)*, J. Combin. Theory Ser. A 99 (2002) 95–110), and products give `112^(k/6)`, i.e.
  `n^{1 + log₃ 112^{1/6}} = n^{1.7155}` triangles instead of `n^{1.63}`. Best known caps in
  dimensions 7–10: `236, 512, 1082, 2432` (Calderbank–Fishburn 1994; Romera-Paredes et al.,
  Nature 625 (2024) 468–475; Edel's tables), all with a worse per-dimension rate than `112^{1/6}`;
  asymptotically `2.218^k` (Tyrrell 2022) against the Ellenberg–Gijswijt bound `2.756^k`.
  An explicit form of the Hill cap: R. Calderbank, W. M. Kantor, *The geometry of two-weight
  codes*, Bull. London Math. Soc. 18 (1986) 97–122; A. E. Brouwer, H. Van Maldeghem, *Strongly
  Regular Graphs*, Cambridge 2022, §10.75.
* **Cayley graphs of symmetric caps** (linear representations of projective caps, Brouwer–Van
  Maldeghem §8.7.1). For a cap `C = -C ∌ 0` in `F₃^k`, the graph `x ~ y ⇔ y - x ∈ C` is locally
  linear with `3^{k-1}|C|/2` triangles: the Games graph SRG(729, 112, 1, 20) gives `f(729) ≥ 13608`,
  the Brouwer–Haemers graph SRG(81, 20, 1, 6) gives `f(81) ≥ 270`. Symmetric caps of size `2·m₂(k-1, 3)`
  come from projective caps; the maximum symmetric sizes in dimensions `1..6` are `2, 4, 8, 20, 40, 112`.
* **Exact small values not yet in the records.** The Kneser graph `KG(6,2)` (15 vertices, 15
  triangles) and the collinearity graph of the generalized quadrangle `GQ(2,4)` (27 vertices, 45
  triangles) attain the upper record `n(n+3)/18`, so `f(15) = 15` and `f(27) = 45`. Neither is a
  record yet (the lower record has `10` and `36` there).

The route taken here is the one the literature dictates: get the tripartite construction from
Mathlib once, then keep improving the 3-AP-free set that feeds it. The record function never
mentions `rothNumberNat` (an oracle); it carries an *explicit computable* lower bound for it.

## Starting record

`V000` (SqueezeBench seed): `pin 3 (fun _ => 1)` — the single triangle `K₃`.

## V001 — baseline claude-opus-5

**Bound.** With `m = ⌊(n-3)/6⌋`,

```
record n = max ( V000 n , (2m+1) · min m 2 )
```

**Idea.** `{0, 1}` is 3-AP-free, so `r₃(m) ≥ min m 2`. Mathlib's
`rothNumberNat_le_ruzsaSzemerediNumberNat` turns that into `(2m+1)·min m 2 ≤ f(6m+3)`, and
`f_mono` carries it from `6m+3` to every `n ≥ 6m+3`; `m = ⌊(n-3)/6⌋` is the largest such `m`.
Folded into V000 with `maxWith`, which covers `n < 9` where the construction is empty.

**Why.** It establishes, once, the transfer lemma `key : (2m+1)·r₃(m) ≤ f(6m+3)` that every
later version reuses, and it already improves V000 at every `n ≥ 9` — an infinite family,
growing linearly.

**Witness.** `n₀ = 15`: `1 → 10`.

## V002 — baseline claude-opus-5

**Bound.** With `m = ⌊(n-3)/6⌋`,

```
record n = max ( V001 n , (2m+1) · 2^⌊log₃ m⌋ )
```

**Idea.** Szekeres' tripling step, proved here as `roth_triple : 2·r₃(m) ≤ r₃(3m)`: if
`A ⊆ [0,m)` is 3-AP-free then so is `3A ∪ (3A+1) ⊆ [0,3m)`, which is twice as large — writing
`a = 3a'+α` etc. with `α, β, γ ∈ {0,1}`, `a + c = 2b` forces `α = β = γ` and `a' + c' = 2b'`.
Iterating from `r₃(m) ≥ 1` gives `r₃(m) ≥ 2^⌊log₃ m⌋`, computed by a fuel-recursive `szAux`
so the kernel evaluates it in `O(log m)` steps. Fed into `key` this gives roughly
`n^{1.63}/3` at powers of three.

**Why.** This is the first bound that is superlinear, and it improves V001 at every `n` with
`⌊(n-3)/6⌋ ≥ 9`, i.e. every `n ≥ 57` — again an infinite family, and by an unbounded factor.

**Witness.** `n₀ = 57`: `38 → 76`.

## V003 — baseline claude-opus-5

**Bound.** With `m = ⌊(n-3)/6⌋`,

```
record n = max ( V002 n , (2m+1) · 5·2^⌊log₃(m/9)⌋ )   for m ≥ 9
```

**Idea.** The same tripling recursion as V002, restarted from a better base case:
`{0, 1, 3, 7, 8} ⊆ [0, 9)` is 3-AP-free, so `r₃(9) ≥ 5`, whereas the pure base-3 digit set gives
only `4`. Bottoming the recursion out at `m = 9` multiplies the Roth bound — and therefore the
triangle bound — by `5/4` at every `m ≥ 27`.

**Why.** It is a cheap, sound `5/4` factor at infinitely many `n` (every `n ≥ 165`), reusing
V002's `roth_triple` and V001's `key` unchanged.

**Witness.** `n₀ = 165`: `440 → 550`.

## V004 — baseline claude-opus-5

**Bound.** With `m = ⌊(n-3)/6⌋` and `sz` the recursion

```
sz m = m                                for m ≤ 2
sz m = 5                                for 9 ≤ m ≤ 11
sz m = sz ⌈m/3⌉ + sz ⌈(m-1)/3⌉          otherwise
record n = max ( V003 n , (2m+1) · sz m )
```

**Idea.** V002/V003 use the *tripling* step `A ↦ 3A ∪ (3A+1)`, which only ever sees the largest
power of three below `m`. The sharper step lets the two residue classes come from **different**
3-AP-free sets: if `A ⊆ [0, ⌈m/3⌉)` and `B ⊆ [0, ⌈(m-1)/3⌉)` are 3-AP-free then `3A ∪ (3B+1)` is
3-AP-free inside `[0, m)` — in `a + c = 2b` the three residues mod 3 must agree, so a progression
stays inside one class and projects to one there. Hence `roth_split`:

```
r₃(m) ≥ r₃(⌈m/3⌉) + r₃(⌈(m-1)/3⌉),      ⌈m/3⌉ = (m+2)/3 and ⌈(m-1)/3⌉ = (m+1)/3 in ℕ.
```

Iterating it counts the **whole** Szekeres set below `m` (the digit-`2`-free integers), not just
the last power of three — item 1 of the old "next improvement" list, and the proof turned out to
need no digit description at all, only the two-set form of the same step.

**Why.** It improves V003 at essentially every `n ≥ 27`, by a factor that oscillates between `1`
(at `m` a power of three, where the two agree) and nearly `2` just below a power of three. Cost:
10867 heartbeats in all.

**Witness.** `n₀ = 249` (`m = 41`): `830 → 1328`.

## V005 — baseline claude-opus-5

**Bound.** With `m = ⌊(n-3)/6⌋`,

```
base m = 0,5,6,9,10,11,12,13,14   at the thresholds m = 0,9,11,20,24,26,30,32,36
sz m   = m                                       for m ≤ 2
sz m   = max (base m) (sz ⌈m/3⌉ + sz ⌈(m-1)/3⌉)  otherwise
record n = max ( V004 n , (2m+1) · sz m )
```

**Idea.** V004's recursion bottoms out in a single base value, `r₃(9) ≥ 5`. Here the base is a
whole table, and it is consulted at **every** level of the recursion, not only at the bottom.
The thresholds are exactly the `M` where the true `r₃(M)` first exceeds what the split recursion
alone produces; each is carried by one explicit 3-AP-free set, found by an exhaustive search run
outside Lean and then *checked* (not searched for) in the proof:

| `M` | 9 | 11 | 20 | 24 | 26 | 30 | 32 | 36 |
|---|---|---|---|---|---|---|---|---|
| set | `{0,1,3,7,8}` | `{0,1,3,4,9,10}` | `{0,1,5,6,8,13,14,17,19}` | `{0,1,4,6,10,15,17,18,22,23}` | `{0,1,4,6,10,15,17,18,22,23,25}` | `{0,2,3,7,8,10,19,21,22,26,27,29}` | `{0,1,3,7,8,10,18,21,22,25,27,30,31}` | `{0,1,3,7,8,12,20,22,25,26,29,31,34,35}` |
| size | 5 | 6 | 9 | 10 | 11 | 12 | 13 | 14 |

3-AP-freeness of a fixed finite set is a finite check on its own elements — `∀ a b c ∈ s,
a + c = b + b → a = b` — so `decide` settles each one; `apFree_of` turns that into Mathlib's
`ThreeAPFree`. This is a check of supplied data, not a kernel search: 60919 heartbeats in all.

**Why.** It raises the bound at about **two thirds of all `n`** (67% of `n < 20000`), by up to
`13/10`, and is the last cheap constant-factor gain available from small sets: above `M = 36` the
split recursion already matches the true Roth number until `M = 47`.

**Witness.** `n₀ = 195` (`m = 32`): `650 → 845`.

## V006 — baseline claude-opus-5

**Bound.** With `m = ⌊(n-3)/6⌋`, V005's recursion over a table extended past `M = 36`:

```
base m = V005.base m   for m < 51,   17 for 51 ≤ m < 69,   20 for m ≥ 69
sz m   = max (base m) (sz ⌈m/3⌉ + sz ⌈(m-1)/3⌉)   for m ≥ 3
record n = max ( V005 n , (2m+1) · sz m )
```

**Idea.** Exactly V005, with two further explicit 3-AP-free sets, found by a randomised greedy
search outside Lean and checked by `decide` in the proof:

* `{0,1,3,4,10,12,13,15,28,32,34,35,37,45,47,48,50} ⊆ [0, 51)`, size `17` (V005's `sz 51 = 16`);
* `{0,1,4,6,10,15,17,18,22,23,25,47,48,52,54,55,59,65,67,68} ⊆ [0, 69)`, size `20`
  (V005's `sz 69 = 18`).

Neither set is claimed optimal — any valid set that beats the recursion at its `M` is a gain, and
the greedy search is much cheaper than the exhaustive one V005 used. `V005.le_roth_of` and
`V004.roth_split` are reused verbatim; only `base_le` is new.

**Why.** It raises the bound at 12% of all `n` (`n < 20000`), by up to `20/18`, and never lowers
it. The `decide` for a set of size `s` costs about `s³` kernel steps, so the two entries take the
file to 44778 of the 200000 heartbeats — the budget is per file, and V006 only repeats the two
new sets, so several more entries would still fit.

**Witness.** `n₀ = 417` (`m = 69`): `2502 → 2780`.

## V007 — trial claude-fable

**Bound.** With `capr = (1, 2, 4, 9, 20, 45)`, `symr = (1, 2, 4, 8, 20, 40)` indexed by `r ≤ 5`,
`capB k = 112^(k/6) · capr (k % 6)`, `symB k = 112^(k/6) · symr (k % 6)`:

```
tripAt n k = 3^k · (2m+1) · capB k · sz m      where q = ⌊n / (3·3^k)⌋ ≥ 1, m = ⌊(q-1)/2⌋   (else 0)
cayAt k    = 3^k · symB k / 6                   used when 1 ≤ k and 3^k ≤ n
record n   = max ( V006 n , max_k tripAt n k , max_k cayAt k )
```

**Idea.** Cap sets instead of integer 3-AP-free sets, in two graphs.

1. *Tripartite.* Mathlib's `addRothNumber_le_ruzsaSzemerediNumber` holds over any finite
   commutative ring with `2` a unit, so it is applied to `Fin (2m+1) × (Fin q → Fin 6 → ZMod 3) ×
   (Fin r → ZMod 3)` with the product of V006's integer set, `q` copies of the Hill cap and one
   small cap: `3^k (2m+1) · 112^q capr r · sz m` triangles on `3·3^k·(2m+1)` vertices.
2. *Cayley.* `CayleyCap` proves, for a group of exponent three and a symmetric cap `S ∌ 0`, that
   the Cayley graph is locally linear (the third vertex of a triangle through `xy` is forced to be
   `-(x+y)`) and has at least `|G|·|S|/6` triangles (`(x, a) ↦ {x, x+a, x+2a}` is at most six to
   one). Applied to `C112^q × symcap r`.

Every cap is a list of base-3 codes; `CapCode.threeAPFree_of_pairwise` reduces `ThreeAPFree` of
the decoded set to one pairwise kernel check ("the third point of the line through two listed
codes is not listed", a bitmask lookup), about 3 heartbeats per pair, so the Hill cap costs
`27698` heartbeats and the whole file `94868`. The caps: the graph of `x² + y²` (9), the cone over
an elliptic quadric (20, symmetric), the Hill cap in Calderbank–Kantor form (112, symmetric), the
Hill cap minus a tangent hyperplane (45), and `{1,2}^3`, `{1,2} × 20` (symmetric 8 and 40).

**Why.** It beats V006 at about 91% of all `n < 20000` (30% of `n < 2000`; first at `n = 9`, where
it reaches the true value `6`), by a factor that grows without bound: `1.8` at `n = 729`, `2.2` at
`n = 59049`, `3.1` at `n = 531441`. It raises the exponent of the lower bound from `1.63` to
`1.7155`.

**Witness.** `n₀ = 729` (the Games graph): `7533 → 13608`.

## V008 — trial claude-fable

**Bound.** With `zt N` the table below (`0` off the table), `zr N = max (zt N) (sz ((N-1)/2))`:

```
zbest q  = max over odd N ≤ q of N · zr N        (the largest odd N ≤ q, and all table N ≤ 99)
tripAt n k = 3^k · capB k · zbest ⌊n / (3·3^k)⌋
record n = max ( V007 n , max_k tripAt n k )
```

| `N` | 1 | 3 | 7 | 9 | 17 | 19 | 21 | 25 | 27 | 35 | 37 | 39 | 45 | 47 | 51 | 57 | 59 | 61 | 63 | 65 | 69 | 71 | 79 | 81 | 85 | 93 | 95 | 97 | 99 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `zt N` | 1 | 2 | 3 | 4 | 5 | 6 | 6 | 7 | 8 | 9 | 10 | 10 | 10 | 10 | 11 | 12 | 12 | 13 | 13 | 14 | 14 | 14 | 15 | 16 | 17 | 17 | 17 | 17 | 17 |
| `sz ((N-1)/2)` | 0 | 1 | 2 | 3 | 4 | 5 | 5 | 6 | 7 | 8 | 8 | 8 | 9 | 9 | 10 | 11 | 11 | 12 | 12 | 13 | 13 | 13 | 14 | 15 | 16 | 16 | 16 | 16 | 16 |

**Idea.** The cyclic factor `Z_{2m+1}` of V007's tripartite construction was filled with the
integer set `[0, m)`; 3-AP-free subsets of `Z_N` itself (no `a + c ≡ 2b (mod N)`) are larger,
e.g. `{0, 1, 3} ⊆ Z_7`. The table holds explicit such sets (exact maxima for `N ≤ 61`, found by a
backtracking search; lower bounds beyond), each checked by the kernel with V007's bitmask trick
(`#L²` steps: for distinct listed `a, b` the residue `2b - a` is not listed), and `zt_le` /
`zr_le` feed them into V007's `trip` in place of `rothNumberNat m`. The odd `N` is also chosen
freely below the room `q` rather than as the largest odd number.

**Why.** It beats V007 at about 63% of all `n < 20000`, by up to `1.5` (`n = 21`: `14 → 21`;
`n = 63`: `105 → 126`; `n = 10005`: `597780 → 631800`), and the gains recur at every scale since
each `k` leaves a small cyclic factor. Cost: 48038 heartbeats in all.

**Witness.** `n₀ = 21`: `14 → 21`.

## Values

| n | 9 | 15 | 57 | 165 | 195 | 249 | 501 | 603 | 1461 | 10005 |
|---|---|---|---|---|---|---|---|---|---|---|
| m = ⌊(n-3)/6⌋ | 1 | 2 | 9 | 27 | 32 | 41 | 83 | 100 | 243 | 1667 |
| V000 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| V001 | 3 | 10 | 38 | 110 | 130 | 166 | 334 | 402 | 974 | 6670 |
| V003 | 3 | 10 | 95 | 550 | 650 | 830 | 3340 | 4020 | 19480 | 266800 |
| V004 | 3 | 10 | 95 | 550 | 650 | **1328** | 3340 | **4221** | 19480 | **426880** |
| V005 | 3 | 10 | 95 | **605** | **845** | 1328 | **3674** | **5226** | **21428** | **480240** |
| V006 | 3 | 10 | 95 | 605 | 845 | 1328 | 3674 | 5226 | 21428 | 480240 |
| V007 | **6** | 10 | 95 | 605 | 845 | **1620** | 3674 | 5226 | 21428 | **597780** |
| V008 | 6 | 10 | **114** | 605 | **910** | 1620 | 3674 | **5460** | 21428 | **631800** |
| true `f(n)` | 6 | 15 | ? | ? | ? | ? | ? | ? | ? | ? |

(V006 beats V005 at 12% of all `n` — for instance at `n = 417`, `2502 → 2780` — but not at the
`n` shown in this table, which were chosen for the earlier versions.)

At powers of three, where the Cayley construction applies (V007 = `3^{k-1} · symB k / 2`):

| n | 27 | 81 | 243 | 729 | 2187 | 6561 | 19683 | 59049 | 177147 | 531441 |
|---|---|---|---|---|---|---|---|---|---|---|
| V006 | 27 | 189 | 1215 | 7533 | 45927 | 277749 | 1673055 | 10058013 | 60407127 | 362619909 |
| V007 | 36 | 270 | 1620 | 13608 | 81648 | 489888 | 2939328 | 22044960 | 132269760 | 1111065984 |
| V008 | 36 | 270 | 1620 | 13608 | 81648 | 489888 | 2939328 | 22044960 | 132269760 | 1111065984 |
| true `f(n)` | 45 | ? | ? | ? | ? | ? | ? | ? | ? | ? |

(Each row is the value of that record, i.e. the max with all earlier ones.)

## What the next improvement would take

(Updated by trial claude-fable after V008; the older items follow, still valid for the `sz` part.)

Scratch files of trial claude-fable (all under `.lake/scratch/RuzsaSzemeredi-Lower/work/`, which
persists between sessions): `caps.py` (SAT search for the Hill cap, the caps as base-3 codes,
`caps.json`, `caps_ck.json` for the Calderbank–Kantor form), `bounds.py` (Python model of the
records V006–V008 for comparing bounds over `n < 20000`), `cyc.py`/`cyc3.py` (search for cyclic
3-AP-free sets, results `cyc.json` for `N ≤ 45` exact and `cyc2.json` for `47 ≤ N ≤ 99`),
`gen8.py` (generates V008's `Def.lean` and `Proof.lean` from the tables), `small.json` and
`LL.lean` (the parked exact-values work), `Big*.lean` (evaluation-cost probes).

1. **Cyclic 3-AP-free sets for the `Z_N` factor** — done in V008 for odd `N ≤ 99`. Larger `N`
   matter less (a large cyclic factor is usually beaten by one more `F₃` factor), but the entries
   above `N = 61` are not known to be optimal and could be improved by a longer search.
2. **Exact values at `n = 15` and `n = 27`** from `KG(6,2)` and `GQ(2,4)` (see the literature
   notes): both meet the upper record `n(n+3)/18`, so a lower record there would *determine*
   `f(15) = 15` and `f(27) = 45`; it would also lift `n = 15..20` (`10 → 15`) and `n = 27..38`
   (`36`/`44 → 45`). The obstacle is formal: Mathlib's decidable instance for `LocallyLinear`
   enumerates all subsets of `Fin 27`, so one needs a hand-rolled check. **Parked work** (trial
   claude-fable, session closed by the maintainers): the graph data — neighbour bitmasks and the
   triangle lists (45 for `GQ(2,4)` in the double-six model `a_i, b_i, c_ij`; 15 for `KG(6,2)`),
   both verified locally linear in Python — is in `.lake/scratch/RuzsaSzemeredi-Lower/work/small.json`,
   and a draft module `.lake/scratch/RuzsaSzemeredi-Lower/work/LL.lean` defines the graph from
   masks (`adjM`, symmetrised) and the four kernel checks: (i) each listed triple is a triangle,
   (ii) every triangle `a < b < c` is listed (guarded by adjacency so the kernel visits only
   `135 · 27` inner cases), (iii) two distinct listed triangles share at most one vertex, (iv)
   every edge lies in a listed triangle. Missing: `Decidable` instances for those four `def`s
   (declare them as in V007's `PairOk`, otherwise `decide` cannot synthesise them — this is where
   the draft stopped), the reasoning lemma from (i)–(iv) to `LocallyLinear` and to
   `#cliqueFinset 3 = T.length` (sort a clique with `lt_trichotomy` to apply (ii); linearity
   gives `EdgeDisjointTriangles`; (iv) gives the second half), the transfer through
   `le_f_of_locallyLinear`, and the record as `patch`es at `15` and `27` (with `f_mono` for the
   `n` in between, or a `maxWith` of a step function). Expected cost: a few tens of thousands of
   heartbeats.
3. **Better caps in fixed dimensions.** `236` in `F₃^7` (vs `224 = 2·112`) is checkable by the
   same pairwise kernel check (`≈ 28000` pairs, `≈ 85000` heartbeats); `512` in `F₃^8`, `1082`,
   `2432` are too large for a brute-force check and would need a structured proof (orbits under an
   automorphism group, or an algebraic description).
4. **Behrend for astronomically large `n`.** Mathlib's `Behrend.bound_aux'` gives
   `d^n / (n d²) ≤ r₃((2d-1)^n)` over `ℝ`, which converts to ℕ floor division at once; the record
   would take the max over `(n, d)` with `(2d-1)^n ≤ m`. A closer estimate puts the crossover
   with `112^(k/6)` near `m ≈ 10^37` (`n ≈ 10^38`), so it improves the record at infinitely many
   `n` but at none that can be written down comfortably; the integer `n`-th roots must be
   computed by a fuel recursion. **Caveat found in this session:** the witness must be evaluated
   by `decide +kernel` through the whole chain V000–V008 within 200000 heartbeats and 8 GB, and a
   scratch attempt to evaluate `V008.record` at `10^38` and `10^60` (both sides of a `<`, no
   sharing) was killed at the 32 GB memory share; a second attempt under a 12 GB virtual-memory
   `ulimit` aborted even at `10^6`, most likely because of the `ulimit` itself (Lean reserves
   large address ranges), so the true cost at `10^6 … 10^20` is still unmeasured. Measure it
   first (`.lake/scratch/RuzsaSzemeredi-Lower/work/Big6.lean` … `Big20.lean`, run without a
   virtual-memory cap); if the chain is too expensive at `10^38`, Behrend cannot be a record.
5. **Beyond products.** Non-product 3-AP-free sets in `F₃^k × Z_N`, or a better `sz` table
   (V006's items below), only move constants.


1. **More base-table entries, at larger `M`.** V006's table stops at `M = 69` because that is as
   far as an exhaustive search for the largest 3-AP-free subset of `[0, M)` got in the time
   available. The next thresholds where the true Roth number overtakes V005's `sz` are around
   `M = 79, 86, 96` (the greedy search already finds `21` in `[0, 79)`); each explicit set found
   there lifts the bound at every `m` whose recursion path passes through that window. The set need not be optimal — any valid set that
   beats `sz M` helps, so a greedy or randomised search outside Lean is enough. The cost in the
   proof is one `decide` per set, about `#s³` kernel steps (`#s = 14` already costs 9648
   heartbeats, `#s = 20` about 28000; V005's file spends 60919 and V006's 44778 of the 200000
   allowed per file), so several more entries fit
   before the budget has to be spent differently — e.g. by proving 3-AP-freeness of a structured
   set by reasoning rather than by `decide`.
2. **A better recursion, not a better base.** The gains from V004/V005 are bounded: the split
   recursion is *exactly* the count of digit-`2`-free integers below `m`, and base values only
   move the constant. Anything genuinely better needs a different construction — Behrend's
   sphere argument, or Elkin/Green–Wolf's refinement of it.
3. **Behrend.** `r₃(m) ≥ m·exp(-c√(log m))` would give `n^{2-o(1)}`, but it needs a computable
   ℕ-valued surrogate for `exp(-c√(log m))` and a from-scratch formalisation of the sphere
   argument; Mathlib's version is ℝ-valued and noncomputable. This is the one step that would
   change the exponent rather than the constant, and it is a large piece of work.
4. **Beyond 3-AP-free sets** — nothing better is known; `f(n) = o(n²)` is the Ruzsa–Szemerédi
   theorem, so the gap to the `C(n,3)` upper record is essentially the whole open problem.

## Problems hit

* (trial claude-fable) Type-class synthesis for `DecidableEq (α ⊕ α ⊕ α)` fails when `α` is the
  nested ring `Fin (2m+1) × (Fin q → Fin 6 → ZMod 3) × (Fin r → ZMod 3)` — the instance term
  exceeds `synthInstance.maxSize`, which a record may not raise. Restating Mathlib's
  `addRothNumber_le_ruzsaSzemerediNumber` for a *variable* ring (`V007.rs_of_ring`) avoids it. A
  local `haveI : DecidableEq α` instead causes instance mismatches (`addRothNumber` terms that
  differ only in the instance) and whnf timeouts.
* `Nat.cast : ℕ → Fin N` is a scoped instance (`Fin.NatCast`/`Fin.CommRing`); V008 builds
  residues with an explicit `Fin.mk` instead.
* The elaborator's `decide` runs out of recursion depth on the record chain (`strict` of V008)
  and on if-chains like `zt`; `decide +kernel` is robust and is what the fuel gate uses anyway.
  `split_ifs` on a 13-way `if` chain also blew up; V008 proves the table lemma by
  `interval_cases` bullets with `decide +kernel` equations and a tail where every `if` is false.
* Kernel checks are cheap: about 3 heartbeats per elementary pair check on ℕ literals with a
  bitmask membership test (V007's 112-cap: 6216 pairs, 27698 heartbeats), so explicit
  combinatorial data of a few thousand pairs is affordable; the elaborator's `#count_heartbeats`
  only counts kernel work with `Elab.async` off.

* Mathlib's own `ruzsaSzemerediNumberNat_lower_bound` is ℝ-valued and noncomputable, and
  `rothNumberNat` is an oracle for this problem, so neither can appear in a record's
  *definition*. Both may be used in the *proofs*, and `rothNumberNat_le_ruzsaSzemerediNumberNat`
  is exactly the bridge that makes this track tractable.
* `f` is `noncomputable` and not decidable, so no small value can be checked by `decide`; every
  bound has to come from an exhibited construction.
