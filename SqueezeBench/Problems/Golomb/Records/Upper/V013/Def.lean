import SqueezeBench.Problems.Golomb.Records.Upper.V012.Def

-- Golomb upper-bound record V013 — the record function.
-- A table of the best known rulers for `m = 81, …, 100` (T. Rokicki and G. Dogon, *Larger Golomb
-- rulers*, data at cube20.org/golomb: each is a window of a Singer or Bose modular ruler
-- for a prime power `q` near `m`, with the best multiplier and rotation found by exhaustive
-- search). None is known to be optimal, but each is far below the record's `(m-1)·q`
-- (`623` against `811` at `m = 29`). Outside the table the bound falls back to the previous
-- record, and the two are folded with `minWith`. Definitions only; validity is proved in
-- `Proof.lean`, where each entry is witnessed by the ruler itself.

namespace SqueezeBench.Golomb.Upper.V013

open SqueezeBench

/-- Best known lengths at the tabulated `m`, the previous record elsewhere. -/
def small (m : ℕ) : ℕ :=
  if m = 81 then 5717
  else if m = 82 then 5814
  else if m = 83 then 6020
  else if m = 84 then 6159
  else if m = 85 then 6410
  else if m = 86 then 6537
  else if m = 87 then 6708
  else if m = 88 then 6745
  else if m = 89 then 6778
  else if m = 90 then 6967
  else if m = 91 then 7542
  else if m = 92 then 7617
  else if m = 93 then 7726
  else if m = 94 then 7884
  else if m = 95 then 7967
  else if m = 96 then 8121
  else if m = 97 then 8357
  else if m = 98 then 8462
  else if m = 99 then 8540
  else if m = 100 then 8831
  else SqueezeBench.Golomb.Upper.V012.record m

/-- The previous record folded with the table. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V012.record small

end SqueezeBench.Golomb.Upper.V013
