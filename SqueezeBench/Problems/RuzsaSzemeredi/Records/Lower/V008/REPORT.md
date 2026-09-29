# RuzsaSzemeredi, lower record, V008

By trial claude-fable.

## How the bound was obtained

**Idea.** V007's tripartite construction over `F₃^k × Z_N` takes its cyclic factor from the
integer 3-AP-free sets of V006 (`[0, m) ⊆ Z_{2m+1}`, `sz m` elements), but 3-AP-free subsets of
the cyclic group `Z_N` itself — no `a + c ≡ 2b (mod N)` with `a ≠ b` — can be larger: `{0, 1, 3}`
in `Z_7` has three elements where `sz 3 = 2`. This version adds a table `zt N` of explicit such
sets for odd `N ≤ 99` at every `N` where they beat `sz ((N-1)/2)` (29 entries), and lets the
construction choose the odd `N` freely below the available room `q = ⌊n / (3·3^k)⌋` instead of
taking the largest one (`zbest`): the bound is `3^k · capB k · max_{N ≤ q odd} N · zr N` with
`zr N = max (zt N) (sz ((N-1)/2))`, maximised over `k`. Everything else (the caps, the Cayley
graphs) is V007, and the record is the maximum with V007.

The sets were found by a backtracking search outside Lean (exact maxima for `N ≤ 61`, the search
being cut off at 15 seconds per `N` above that, so the larger entries are lower bounds only); for
`N ≤ 45` they agree with the exact values `1, 2, 2, 3, 4, 4, 4, 4, 5, 6, 6, 6, 7, 8, 8, 8, 8, 9,
10, 10, 9, 9, 10` of the maximum 3-AP-free subsets of `Z_1, Z_3, …, Z_45`.

**Why.** It beats V007 at about 61% of all `n < 20000`, by a factor of up to `1.5` (`n = 21`:
`14 → 21`; `n = 63`: `105 → 126`; `n = 105`: `280 → 315`; `n = 10005`: `597780 → 631800`), and
the gains recur at every scale because each `k` leaves a small cyclic factor.

## How the proofs were obtained

Written by the AI agent named below, interactively against the compiler.

* Each table entry is a list of residues checked by the kernel with the bitmask trick of V007:
  for two distinct listed residues `a, b` the residue `2b - a (mod N)` is not listed (`CycOk`),
  `#L²` steps per entry; `threeAPFree_cyc` turns the check into `ThreeAPFree` of the residue set
  in `Fin N` (`Fin.val_add`, then `Nat.ModEq.add_right_cancel'` to identify the third residue),
  and `le_addRothNumber_of_cyc` gives `zt N ≤ addRothNumber (univ : Finset (Fin N))`.
* `zt_le` is a case split on `m < 50` (one bullet per residue class, the value of `zt` settled by
  `decide +kernel`) and the tail `m ≥ 50` where every `if` is false.
* `trip` is V007's proof with the cyclic Roth number of `Fin (2m+1)` in place of
  `rothNumberNat m`; `tbAux_le`/`zbest_le` bound the `max` term by term through `f_mono`.
* `strict` at `n₀ = 21`: `14 → 21`, by `decide +kernel` (the elaborator's `decide` runs out of
  recursion depth on the chain of records).

The whole file uses about 50000 heartbeats.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as the agent, in Claude Code; Lean 4 / Mathlib as
  pinned by the project.
- Machine: 96 CPUs, 755 GB RAM (32 GB share), Linux 6.8.0-124-generic.
- Time: about two hours. Outside Lean: a Python backtracking search for 3-AP-free subsets of
  `Z_N` (exact for `N ≤ 61`, 15 seconds per `N` beyond), Python verification of every set, and a
  comparison of the new bound with V007 over `n < 20000`.
