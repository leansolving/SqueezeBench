# Ramsey, lower record, V010

By trial claude-fable.

## How the bound was obtained

Spencer's lower bound (J. Spencer, *Ramsey's theorem — a new lower bound*, J. Combin.
Theory A 18 (1975) 108–115), obtained from the symmetric Lovász Local Lemma (Erdős–Lovász
1975) applied to the events "the `n`-set `S` is monochromatic" in a random 2-colouring of
`K_N`. Each event has probability `p = 2^(1−C(n,2))` and depends on at most
`d = C(n,2)·C(N−2, n−2)` others, so the `4pd ≤ 1` form of the lemma (see e.g. Alon–Spencer,
*The Probabilistic Method*, Ch. 5, or Edmonds–Paulson, CPP 2024, for the two variants)
gives `R(n,n) > N` whenever `8·C(n,2)·C(N−2,n−2) ≤ 2^C(n,2)`. Asymptotically this is
`(√2/e)(1+o(1))·n·2^(n/2)`, the best known lower bound on the diagonal Ramsey numbers; the
`4pd` form loses only the factor `(e/4)^(1/(n−2))` against the `e·p·(d+1) ≤ 1` form and
needs no bound on `(1+1/d)^d`. The record uses the search-friendly sufficient condition
`8·C(n,2)·(N−2)^(n−2) ≤ (n−2)!·2^C(n,2)` and takes the largest such `N` by a binary search
inside the record, as V006 does. It beats V007's alteration bound at every `n ≥ 19`, by a
factor tending to `√2`.

A numeric comparison of the candidate forms (Python) preceded the choice; a consultation
of a second model (GPT) confirmed the proof architecture — cleared denominators, the
conditional bound first and positivity afterwards, the `4pd` form to avoid `e` — and pointed
to an independent Lean development with the same structure, which was not used.

## How the proofs were obtained

Written by hand by the submitter (an AI agent), on top of V006's colourings, monochromatic
sets, pairs and graph, and reusing the shape of V006's search invariant.

- **Events.** `bad S` is the set of colourings monochromatic on `S`, `avoid Y` those
  monochromatic on no member of `Y` (the conditioning event `∩_{T∈Y} A_Tᶜ`).
- **The fibre count** (`card_bad_inter_le`): if membership in `B` depends only on the
  values outside the pairs of `S`, then `|bad S ∩ B| · 2^C(|S|,2) ≤ 2 · |B|`. Both sides
  are counted fibrewise over the restriction to the outside pairs: a fibre of `bad S ∩ B`
  injects into `Bool` (the colour), and a fibre of `B` over a restriction in its image
  contains every gluing of an inside assignment with that restriction, `2^C(|S|,2)` of them
  (`Finset.card_le_mul_card_image`, `Finset.card_eq_sum_card_image`).
- **Independence** (`mono_congr`, `detOff_avoid`): a set `T` with `|T ∩ S| ≤ 1` has no pair
  inside `S`, so `Mono c T` is determined outside `S`, and so is `avoid Y` for a family of
  such `T`.
- **The dependency count** (`card_dep_le`): the members of `Y` sharing two vertices with
  `S` are covered by the `C(n,2)` families `{T : Q ⊆ T}`, `Q` a 2-subset of `S`, each of
  size at most `C(N−2, n−2)` (`T ↦ T \ Q` injects into the `(n−2)`-subsets of `univ \ Q`).
- **The local lemma** (`main_ind`): strong induction on `|Y|`, generalised over `S`.
  Split `Y` into the members sharing a pair with `S` (`Y₁`, at most `d`) and the rest
  (`Y₂`); then `|bad S ∩ avoid Y| ≤ |bad S ∩ avoid Y₂| ≤ 2·|avoid Y₂|/2^C` by the fibre
  count, and `avoid Y₂ \ avoid Y` is covered by the sets `bad T ∩ avoid Y₂`, `T ∈ Y₁`, each
  of size at most `4·|avoid Y₂|/2^C` by the induction hypothesis (`|Y₂| < |Y|` as soon as
  `Y₁` is nonempty), so `|avoid Y₂| ≤ 2·|avoid Y|` when `8d ≤ 2^C`. All of it in `ℕ` with
  the powers of two multiplied out.
- **Positivity** (`avoid_pos`): `Finset.induction_on`; adding a set removes at most
  `4/2^C < 1` of the colourings, so `avoid 𝒫` is nonempty; V006's graph of such a
  colouring refutes `Forces N n n`.
- `improves`: `maxWith_improves`. `strict`: `decide` at `n₀ = 20`, `7438 → 7569`.

No computation beyond the record's own search at the witness; the whole file is reasoning (47k heartbeats, 31k of them the set identity `avoid (insert T Y) = avoid Y \\ (bad T ∩ avoid Y)` in `avoid_pos`).

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; Lean 4.31.0 with the pinned
  Mathlib; Python for the numeric comparison; one consultation of GPT (see above).
- Machine: 96 cores, 755 GB RAM (32 GB available to this session), Linux 6.8.0.
- Time spent: about three hours. No computation outside Lean beyond the numeric
  comparison of bounds.
