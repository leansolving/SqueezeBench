# Roth, lower record, V007

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = max(V006, c₇)` where `c₇` is the last-digit recursion of V002–V006 with the
base window widened from `n ≤ 56` to `n ≤ 209` and filled with the exact Roth numbers there:

    c₇ n = r₃(n)                                          (n ≤ 209, from the table `tblList`)
    c₇ n = max (r₃(209)) (c₇ ⌈n/3⌉ + c₇ ⌈(n-1)/3⌉)         (n ≥ 210)

**Idea.** The exact values `r₃(n)` are known for `n ≤ 211` (OEIS A003002: Dybizbański 2012 up to
`n = 123`, extended to `211` in the OEIS b-file by F. A. C. Cariboni), and the OEIS a-file of
A003002 (compiled by Cariboni, 2018, from sets of Wagstaff, Gasarch, Wróblewski and others)
prints an extremal set for every `n = 4 … 209`. The record only needs one certificate per *jump
node* of `r₃` (an `n` with `r₃(n) > r₃(n-1)`): a set of size `r₃(n)` inside `[0, n)` also
certifies every `n'` up to the next jump node, because `r₃` is constant there. There are 43
jump nodes up to `209`; the two smallest sets (`{0}`, `{0, 1}`) are not in the a-file and were
written by hand, and the empty set stands for `n = 0`.

The V006 window was not exact: the V005/V006 recursion is short of `r₃(n)` at 118 of the `n ≤ 211`,
already at `n = 30, 31, 32, 36, 37` and `51 … 57` inside the old window, and by up to `5` at
`n = 209` (`38` against `43`). The recursion above the window is multiplicative in its base, so the
gain propagates: `c₇ 243 = 44` against `40`, `c₇ 729 = 88` against `78`, `c₇ 1000 = 116` against
`105`; the new record is strictly larger at almost every `n ≥ 30` (all `n` whose splitting tree
reaches an improved entry).

**Why this bound.** It is item 1 of the notes left after V006 (widen the base window), carried
out all the way to the end of the known values with published certificates instead of a search.
Everything the known values offer to the recursion is now in the record; further gains need
either new sets above `n = 211` or a better recursion (see the track report).

## How the proofs were obtained

Written by the submitter (an AI agent) by hand, reusing the V004 plumbing (`below`, `below_le`)
and the V002 split lemma (`split_le`); the fuel induction is the one of V005/V006.

The certificates are checked in the kernel by `decide +kernel`, but with a **quadratic** check
instead of the cubic one of V004–V006: for a list `l` with bitmask `m`, `chk l m` tests, for every
pair `a < b` in `l`, that the third term `2b - a` is not in `m` (`Nat.testBit`, a kernel-accelerated
shift and mask). `free_of_chk` turns this into the `∀ a b c ∈ l, a + c = b + b → a = c` form that
`below_le` needs: a progression with `a ≠ c` has its smaller endpoint below the middle, and the
check rules out its larger endpoint. For the 32-element set the cubic kernel check costs 16642
heartbeats (in thousands) and the quadratic one 716, so all 44 certificates together fit in about
26000; the cubic version would have needed more than a million.

The table is connected to the certificates by a second `decide +kernel` (`tblOK`): for every
`n < 210`, the first certificate whose jump node is at most `n` has at least `tblList[n]` elements
below `n`. The certificates are listed largest jump node first so that `List.any` stops at the
right one after a single comparison per skipped set; a naive maximum over all sets costs 116000.

Nothing was hard; the first build failed only because `n = 0` had no certificate (fixed with the
empty set) and because `simp` had already rewritten the inner `List.all`.

## Setup

- Tools: Claude Fable 5.1 (Anthropic) through Claude Code, with GPT-6 Astra consulted once on
  the literature (it pointed to the OEIS a-file and to a modular product construction recorded
  in the track report for the next version). Python 3 checked every set and computed the values
  of the recursion outside Lean; Lean 4.31.0 with the pinned Mathlib.
- Machine: 96 CPUs, 755 GB memory (32 GB share), Linux 6.8.0-124-generic.
- Time: about two hours from reading the track to `ACCEPT`, most of it reading and measuring
  kernel costs. Computation outside Lean: a few seconds of Python.
- Sources: OEIS A003002 (b-file and a-file, <https://oeis.org/A003002>); J. Dybizbański,
  *Sequences containing no 3-term arithmetic progressions*, Electron. J. Combin. 19(2) (2012),
  #P15 (extremal sets for jump nodes `n ≤ 123`, which agree in size with the a-file).
