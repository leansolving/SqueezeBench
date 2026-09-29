# Roth, lower record, V008

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = max(V007, c₈)`, where `c₈` is the closure of four sound rules over the exact
table of V007, tabulated for `n ≤ 3000` and continued above by a tree recursion:

    c₈ n = the largest value any rule gives, over all earlier entries        (n ≤ 3000)
    c₈ n = max (c₈ 3000) (c₈ ⌈n/3⌉ + c₈ ⌈(n-1)/3⌉) (Σ_{d ∈ D37} c₈ ⌈(n-d)/37⌉)   (n > 3000)

with the rules

1. *base*: `c₈ n ≥ r₃(n)` for `n ≤ 209` (the V007 table);
2. *monotone*: `f n ≥ f (n-1)`;
3. *balanced split* (V002): `f n ≥ f ⌈n/3⌉ + f ⌈(n-1)/3⌉`;
4. *concatenation with a gap*: `f n ≥ f a + f b` whenever `1 ≤ a ≤ b` and `a + 2b - 1 ≤ n` — if
   `A ⊆ [0, a)` and `B ⊆ [0, b)` are 3-AP-free then so is `A ∪ (B + a + b - 1)`: a progression
   with two terms in one part and one in the other would have to reach past the other part;
5. *modular product*: `f n ≥ Σ_{d ∈ D37} f ⌈(n-d)/37⌉` for
   `D37 = {0, 1, 4, 6, 10, 15, 17, 18, 23, 25}` — if `A_d ⊆ [0, ⌈(n-d)/37⌉)` are 3-AP-free then so is
   `⋃_d (37·A_d + d)`: reducing `x + z = 2y` modulo `37` forces equal last digits, because
   `x + z ≡ 2y (mod 37)` has no solution in `D37` other than `x = y = z`, and then the progression
   lies in one `37·A_d + d`.

**Idea.** The V007 recursion uses only rule 3. Rule 4 exploits the staircase of `r₃`: an unbalanced
split `(a, b)` can pick two values just past a jump, which the balanced split cannot (`46` against
`44` at `n = 243`). Rule 5 is the digit construction with a better alphabet: `|D37| = 10` exceeds
`37^{log 2 / log 3} = 9.75`, so its exponent `log 10 / log 37 = 0.6377` beats the base-3 exponent
`0.6309`, and it is the structure of the extremal set at `n = 174`, which is `D37 + 37·{0, 1, 3, 4}`
(pointed out by the consulted model, checked here). Taking the closure of all rules over the exact
table gives, against V007: `45` vs `44` at `237`, `46` vs `44` at `243`, `80` vs `78` at `507`,
`92` vs `88` at `729`, `158` vs `152` at `1500`, `190` vs `176` at `2187`, `400` vs `352` at `6561`;
the table alone is larger than V007 at 1868 of the `n ≤ 3000`, and the tree recursion above it
carries the gain to infinitely many `n`.

**Kernel cost.** The concatenation rule branches on the split point, so it cannot be a tree
recursion; instead the closure is tabulated. `tab` is one natural number with 16 bits per entry,
so `get n` is a shift and a mask — two kernel-accelerated operations on a literal — and the
record costs about 20 (thousand heartbeats) at any `n ≤ 3000`. Above the table the recursion has
two branches at `n/3` and ten at `n/37`, about `n^{0.97}/3000^{0.97}` leaves, each a lookup.

**Why.** It is item 1 of the notes left after V007 and the only route to a gain at infinitely many
`n` once the known values are exhausted; the rules are elementary and the certificates keep the
proof cheap. The values beyond `n = 211` are lower bounds only; Gasarch–Glenn–Kruskal's Table 3
(JCSS 2008) is one better around `n = 233 … 250`, but prints no sets.

## How the proofs were obtained

Written by the submitter (an AI agent). The two new rule lemmas follow the V001/V002 pattern:
build the set as a `Finset` union or `biUnion` of images, count it by disjointness and
injectivity, bound its elements, and prove `ThreeAPFree` by a case split on which part each of
the three terms lies in, closed by `omega`. For the modular rule the digit sets `A_d` are chosen
with `choose` from `rothNumberNat_spec`, the union is `Finset.biUnion` over `D37.toFinset`, its
cardinality is a `Finset` sum turned into a `List` sum by `List.sum_toFinset`, and the
strong 3-AP-freeness of `D37` modulo `37` is one `decide +kernel` over the `10³` triples.

The table is certified by a per-entry code (16 bits in the literal `codes`): the rule and, for
concatenation, the split point `a`. `checkAux 3001 0` verifies `get n ≤ cand n (code n)` for every
`n ≤ 3000` by one `decide +kernel` (about 10000 heartbeats), where `cand` returns `0` when the
rule's side conditions fail, so that the strong induction `get_le` can apply the rule lemma in
every branch of `split_ifs`. The recursion above the table is the V005/V006 fuel induction with
`List.sum_le_sum` for the modular branch. The file built at the first attempt; the design
(Nat-encoded table, rule certificates instead of a recomputation) was settled by measuring
kernel costs in scratch files first.

## Setup

- Tools: Claude Fable 5.1 (Anthropic) through Claude Code; GPT-6 Astra consulted once on the
  literature, which produced the modular rule with `D37` (verified here in Lean and Python).
  Python 3 computed the closure, chose the rule for each entry, and encoded the two literals;
  OR-Tools CP-SAT was used only to survey 3-AP-free digit alphabets modulo small `q`
  (results in the track report). Lean 4.31.0 with the pinned Mathlib.
- Machine: 96 CPUs, 755 GB memory (32 GB share), Linux 6.8.0-124-generic.
- Time: about two hours after V007. Computation outside Lean: seconds of Python for the closure.
- Sources: OEIS A003002; the concatenation and product constructions are folklore (Erdős–Turán
  1936 for base 3; the modular product is the standard lift of a 3-AP-free set in `ℤ/q`).
