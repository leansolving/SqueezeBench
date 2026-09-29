# RuzsaSzemeredi, lower record, V007

By trial claude-fable.

## How the bound was obtained

**Idea.** All earlier versions feed integer 3-AP-free sets (Szekeres' digit construction with a
table of small base cases) into Mathlib's tripartite Ruzsa–Szemerédi construction. This version
replaces the integers by **cap sets**: in `F₃^k` a 3-AP `a + c = 2b` is the same as a line
`a + b + c = 0`, and caps (sets with no three collinear points) are much larger than digit sets.
The Hill cap has `112` points in `F₃^6` where the digit set `{0,1}^6` has `64`, and products
of Hill blocks give `112^(k/6)` points in `F₃^k`, i.e. exponent `log₃ 112^(1/6) = 0.7155` instead
of `log₃ 2 = 0.6309`. Two graphs are built from caps:

1. **Tripartite** (Mathlib's `addRothNumber_le_ruzsaSzemerediNumber`, valid over any finite
   commutative ring in which `2` is a unit) over the ring `Z_{2m+1} × F₃^(6q) × F₃^r`, `r ≤ 5`,
   with the product of V006's integer set (size `sz m`), `q` Hill blocks and one small cap of
   size `capr r ∈ {1, 2, 4, 9, 20, 45}`: `3^k (2m+1) · 112^q capr r · sz m` triangles on
   `3 · 3^k · (2m+1)` vertices, `k = 6q + r`.
2. **Cayley graph** of a *symmetric* cap `C = -C ∌ 0` in `F₃^k`, `x ~ y` iff `y - x ∈ C`. Its
   triangles are exactly the affine lines `{x, x+a, x-a}`, `a ∈ C`, each edge lies in exactly
   one of them, so the graph is locally linear with `3^(k-1) · |C| / 2` triangles on `3^k`
   vertices. For `k = 6` and the Hill cap this is the Games graph, the strongly regular graph
   `(729, 112, 1, 20)`; the small symmetric caps have sizes `symr r ∈ {1, 2, 4, 8, 20, 40}`.

The record is the maximum of V006 and of both constructions over all admissible `k` (the
`Z_{2m+1}` factor of the tripartite one fills the gaps between powers of three). It beats V006 at
about 91% of all `n < 20000` (30% of `n < 2000`), by a factor that grows without bound: `2.0` at
`n = 9` (where it reaches the true value `f(9) = 6`), `1.8` at `n = 729`, `2.2` at `n = 59049`,
`3.1` at `n = 531441`.

**The caps.** Every cap is supplied as an explicit list of base-3 codes and *checked* by the
kernel, not searched for:

* `9` in `F₃^3`: the graph `{(x, y, x² + y²)}`.
* `20` in `F₃^4`: the nonzero solutions of `x₀² + x₁² + x₂² + 2x₃² = 0`, the cone over an
  elliptic quadric of `PG(3,3)`; symmetric.
* `112` in `F₃^6`: the Hill cap (R. Hill, *On the largest size of cap in S₅,₃*, Atti Accad. Naz.
  Lincei Rend. 54 (1973) 378–384), in the Calderbank–Kantor form (R. Calderbank, W. M. Kantor,
  *The geometry of two-weight codes*, Bull. London Math. Soc. 18 (1986) 97–122; also
  A. E. Brouwer, H. Van Maldeghem, *Strongly Regular Graphs*, §10.75): with coordinates indexed
  by `∞, 0, 1, 2, 3, 4`, the vectors supported on one of the ten triples
  `∞01, ∞12, ∞23, ∞34, ∞40, 013, 124, 023, 134, 024` with nonzero entries there (`10 · 8`), and
  the vectors with all six entries nonzero and product `1` (`32`). It is symmetric, lies on the
  elliptic quadric `∑ xᵢ² = 0` and meets every line of that quadric in two points (a
  hemisystem). A SAT search (a hemisystem of the 112-point quadric, 280 lines, "exactly two of
  four") found an equivalent copy first; the published form was then taken for the record.
* `45` in `F₃^5`: the Hill cap minus a tangent hyperplane meeting it in `11` points, here the
  points with `x_∞ + x_0 + x_1 = 1` in the coordinates `x_0, …, x_4` (Y. Edel, S. Ferret,
  I. Landjev, L. Storme, *The classification of the largest caps in AG(5,3)*, J. Combin. Theory
  Ser. A 99 (2002) 95–110, which also proves the `20`-cap and the `45`-cap unique).
* `8 = {1,2}^3` and `40 = {1,2} × (20-cap)`: symmetric products.

The Cayley-graph view of a cap is the classical *linear representation* of a projective cap
(Brouwer–Van Maldeghem §8.7.1; R. A. Games, *The packing problem for projective geometries over
GF(3) with dimension greater than five*, J. Combin. Theory Ser. A 35 (1983) 126–144 for the
Games graph). Products of Hill blocks are used because `112^(1/6) = 2.195` beats the best known
caps in dimensions 7–10 (`236, 512, 1082, 2432`, rates `≤ 2.183`).

## How the proofs were obtained

Written by the AI agent named below, interactively against the compiler.

* `CapCode`: base-3 codes for vectors of `F₃^k` (`dec`), digit-wise addition and negation
  (`add3`, `neg3`) with the lemmas `dec_add`, `dec_neg`, `dec_inj`, a bitmask membership test
  (`mask`, `testBit_mask`), and `threeAPFree_of_pairwise`: if for every two distinct listed codes
  the third point of their line is not listed, the decoded set is `ThreeAPFree`. The kernel
  checks each list by `decide +kernel` (in range, no repetition, the pairwise check, and for the
  symmetric caps closure under negation and `0 ∉`). The 112-cap costs about `18000` heartbeats
  (6216 pairs); the whole file stays well inside the budget.
* `CayleyCap`: for a finite abelian group of exponent three and a symmetric cap `S ∌ 0`, the
  Cayley graph is locally linear (`third_eq`: the third vertex of a triangle through `xy` is
  `-(x+y)`, hence `triangle_eq`), and `card_mul_le`: `(x, a) ↦ {x, x+a, x+2a}` maps `G × S`
  into the triangles at most six to one (`offDiag_card`), so `|G| · |S| ≤ 6 · #triangles`.
* `trip`: Mathlib's `addRothNumber_le_ruzsaSzemerediNumber` over
  `Fin (2m+1) × (Fin q → Fin 6 → ZMod 3) × (Fin r → ZMod 3)`; `2` is a unit by
  `ZMod.unitOfCoprime`, `Prod.isUnit_iff`, `Pi.isUnit_iff`; the 3-AP-free set is the product
  (`le_addRothNumber_product`, `threeAPFree_pi` for the `q` Hill blocks) of
  `Fin.addRothNumber_eq_rothNumberNat` and the caps. Restating the lemma for a variable ring
  (`rs_of_ring`) avoids a type-class term-size failure on the nested `Sum` type.
* `valid` glues both through `f_mono`; `improves` is `maxWith_improves`; `strict` is `decide`
  at `n₀ = 729`: `7533 → 13608`.

Abandoned: proving the Hill cap by reasoning (hemisystem structure or its automorphism group);
the kernel check turned out cheap enough (about 3 heartbeats per pair).

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as the agent, in Claude Code; one consultation of
  GPT-6 Astra for the literature on the Hill cap and for cap-set tables; Lean 4 / Mathlib as
  pinned by the project.
- Machine: 96 CPUs, 755 GB RAM (32 GB share), Linux 6.8.0-124-generic.
- Time: about five hours in all. Outside Lean: a Python/SAT (`pysat`, Glucose) search for a
  hemisystem of the elliptic quadric `Q⁻(5,3)` (instant), Python verification of every cap and
  of the record values, and a comparison of the new bound with V006 over `n < 20000`.
