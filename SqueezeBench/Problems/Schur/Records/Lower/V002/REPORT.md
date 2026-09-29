# Schur, lower record, V002

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = maxWith V001.record H`, where `H` is the dynamic programme

```
H 0 = 0,  H 1 = 1,  H 2 = 4,  H 3 = 13,  H 4 = 44,  H 5 = 160,  H 6 = 536,  H 7 = 1680,
H (k+8) = max (3·H(k+7) + 1) (33·H(k+5) + 6) (111·H(k+4) + 43) (380·H(k+3) + 148).
```

It reproduces the best published lower bounds on `S(k)` for every `k ≤ 12` except `k = 7, 12`
(`S(7) ≥ 1696` of Rowley 2021 is not included, see below) and beats V001
(`h(k) ≥ 89·3^(k−4)`) at every `k ≥ 5`: `160 > 133` at `k = 5`, `536 > 400`, `1680 > 1201`,
`5286 > 3604`, `17803 > 10813`, `60948 > 32440`, and asymptotically by the factor
`(380^(1/5)/3)^k ≈ 1.094^k` (growth rate `380^(1/5) ≈ 3.28` against `3`).

**Sources.**

* The construction is the S-template method: F. Rowley, *A generalised linear Ramsey graph
  construction*, Australas. J. Combin. 81 (2021) 245–256, as formulated for Schur numbers by
  R. Ageron, P. Casteras, T. Pellerin, Y. Portella, A. Rimmel, J. Tomasik, *New lower bounds for
  Schur and weak Schur numbers*, arXiv:2112.03175 (2022), Definition 2.1 and Theorem 2.3. An
  S-template of width `q` with `n + 1` colours is a sum-free colouring of `[1, q]` whose `n`
  non-special classes are also sum-free modulo `q`; with a sum-free `k`-colouring of `[1, p]`
  it gives a sum-free `(n + k)`-colouring of `[1, pq + m − 1]`, `m` the least special element.
  The Abbott–Hanson product `S(m+n) ≥ (2S(m)+1)·S(n) + S(m)` is the special case of the template
  `[1, a]` + special block `[a+1, 2a+1]`; the tripling `S(k+1) ≥ 3S(k)+1` is the width-3 template.
* The templates of widths 33 (4 colours, `m = 7`), 111 (5 colours, `m = 44`) and 380
  (6 colours, `m = 149`) are Tables 5–7 of Ageron et al. (Appendix A). In the printed width-111
  table the element 49 is missing; both classes 1 and 4 are consistent with all constraints, and
  class 1 was used. Every template was re-verified by an independent script before being
  packed, and is verified again by the kernel in `Proof.lean`.
* The base partitions: `[1, 44]` is V001's `col4` (Golomb–Baumert); `[1, 160]` into 5 sets is
  G. Exoo, *A lower bound for Schur numbers and multicolor Ramsey numbers of K₃*, Electron. J.
  Combin. 1 (1994) #R8 (symmetric, listed there for `1..80`); `[1, 536]` into 6 and `[1, 1680]`
  into 7 sets are H. Fredricksen, M. M. Sweet, *Symmetric sum-free partitions and lower bounds
  for Schur numbers*, Electron. J. Combin. 7 (2000) #R32 (symmetric, listed for the smaller
  element of each pair; for 536, `537 = 3·179`, and 179 and 358 lie in different sets as the
  paper allows).

The known values `S(k) = 1, 4, 13, 44, 160` are not used as theorems; every value of `H` is
attained by an explicit colouring built in the proof.

**Not included.** Rowley's `S(7) ≥ 1696` (arXiv:2107.03560) is only available as a spreadsheet
attachment and was not integrated; with it `H 7`, `H 12` (`644628`) and their descendants would
grow slightly. The 2026 "shifted template" `S(k+2) ≥ 10S(k) + 2` (arXiv:2607.15034) would improve
`k = 8, 13, 18, …`. Both are natural next versions.

## How the proofs were obtained

Written by the AI agent named below, from the construction in the papers, with these design
choices:

* `SF k N c` (sum-free `k`-colouring of `[1, N]`, colours `< k` only required on `[1, N]`) and
  `Good k N := ∃ c, SF k N c`; `le_f_of_SF` turns it into `N ≤ f k` through `Schur.le_f`, using
  `Finite.lean`'s well-posedness, by extending the colouring to `Fin k` outside `[1, N]`.
* `IsTemplate n q m c` (a `Prop` structure) and `tmplApply c n q g`, which colours
  `x = (α−1)q + u`, `u ∈ [1, q]`, by `c u` if `c u < n` and by `n + g α` otherwise.
  `sf_tmplApply : IsTemplate n q m c → SF l p g → SF (n + l) (p·q + m − 1) (tmplApply c n q g)`
  is the paper's Theorem 2.3, proved by the paper's four-case argument; the arithmetic of rows
  and columns is isolated in `row_col_add` (the column and row of `x + y` from those of `x` and
  `y`) and `row_le_of_special` (a special column in `[1, pq + m − 1]` forces row `≤ p`).
* The data are lists of bitsets, one `ℕ` per colour class (bit `x` set iff `x` is in the class),
  coloured by `colOf` (index of the first class containing `x`). Four `Bool` checkers are
  evaluated by the kernel with `decide +kernel`: `chk a N` (`(a <<< x) &&& a = 0` for every
  `x < N` in `a`: no `x + y ∈ a`), `chkW a q N` (the same for `((a <<< x) >>> q) &&& a`: no
  `x + y − q ∈ a`), `chkBelow`, `chkCov`. They are written with `Nat.rec` rather than bounded
  quantifiers, which the probe showed to be about ten times cheaper per step; `Nat.shiftLeft`,
  `Nat.land`, `Nat.shiftRight`, `Nat.testBit` are GMP-accelerated in the kernel, so checking the
  `[1, 1680]` partition costs 6676 heartbeats (`good7`). `sf_colOf` and `isTemplate_colOf`
  turn the checks into `SF` and `IsTemplate` through `Nat.testBit_shiftLeft`, `Nat.testBit_land`,
  `Nat.testBit_shiftRight`, `Nat.testBit_lor`.
* `good_H : ∀ k ≥ 1, Good k (H k)` is a strong induction unfolding `H (j + 8)`; `good_max` uses
  that a sum-free colouring of `[1, N]` restricts to any `[1, M]`, `M ≤ N` (`good_mono` is the
  general form). `v_valid` is then `le_f_of_SF`, and `valid`, `improves`, `strict` are the
  `maxWith` idiom with witness `n₀ = 5` (`133 < 160`).

Budget: 47211 heartbeats in all; heaviest `sf_tmplApply` 10254, `good7` 6676, `row_col_add`
5973. Nothing was hard once the right construction was identified; the earlier report's belief
that the product needs symmetric sum-free partitions of `ℤ_{2N+1}` (which do not exist at
`N = S(k)`) was the main obstacle, and the template formulation removes it.

## Setup

- Tools: Claude Fable 5.1 (Anthropic, `claude-fable-5-1`) as the agent, in Claude Code; a
  consultation of GPT-6 Astra for the literature (pointers to arXiv:2107.03560 and
  arXiv:2607.15034); Lean 4.31.0 with Mathlib as pinned; Python 3.12 scripts for parsing the
  published tables, verifying every partition and template independently, and packing bitsets.
- Machine: 96 CPUs, 755 GB RAM (32 GB allotted), Linux 6.8.0-124-generic.
- Time: about three hours, of which most went into the Lean proof of `sf_tmplApply` and the
  bitset lemmas; no search ran outside Lean (all constructions are published).
