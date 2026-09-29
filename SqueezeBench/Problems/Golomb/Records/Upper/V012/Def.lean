import SqueezeBench.Problems.Golomb.Records.Upper.V011.Def

-- Golomb upper-bound record V012 — the record function.
-- A table of the best known rulers for `m = 29, …, 80` (T. Rokicki and G. Dogon, *Larger Golomb
-- rulers*, data at cube20.org/golomb: each is a window of a Singer or Bose modular ruler
-- for a prime power `q` near `m`, with the best multiplier and rotation found by exhaustive
-- search). None is known to be optimal, but each is far below the record's `(m-1)·q`
-- (`623` against `811` at `m = 29`). Outside the table the bound falls back to the previous
-- record, and the two are folded with `minWith`. Definitions only; validity is proved in
-- `Proof.lean`, where each entry is witnessed by the ruler itself.

namespace SqueezeBench.Golomb.Upper.V012

open SqueezeBench

/-- Best known lengths at the tabulated `m`, the previous record elsewhere. -/
def small (m : ℕ) : ℕ :=
  if m = 29 then 623
  else if m = 30 then 680
  else if m = 31 then 747
  else if m = 32 then 784
  else if m = 33 then 859
  else if m = 34 then 938
  else if m = 35 then 987
  else if m = 36 then 1005
  else if m = 37 then 1099
  else if m = 38 then 1146
  else if m = 39 then 1252
  else if m = 40 then 1282
  else if m = 41 then 1305
  else if m = 42 then 1397
  else if m = 43 then 1507
  else if m = 44 then 1596
  else if m = 45 then 1687
  else if m = 46 then 1703
  else if m = 47 then 1804
  else if m = 48 then 1887
  else if m = 49 then 1958
  else if m = 50 then 2094
  else if m = 51 then 2190
  else if m = 52 then 2270
  else if m = 53 then 2347
  else if m = 54 then 2373
  else if m = 55 then 2598
  else if m = 56 then 2725
  else if m = 57 then 2773
  else if m = 58 then 2851
  else if m = 59 then 2911
  else if m = 60 then 3019
  else if m = 61 then 3134
  else if m = 62 then 3215
  else if m = 63 then 3391
  else if m = 64 then 3527
  else if m = 65 then 3593
  else if m = 66 then 3757
  else if m = 67 then 3819
  else if m = 68 then 3956
  else if m = 69 then 4145
  else if m = 70 then 4217
  else if m = 71 then 4330
  else if m = 72 then 4473
  else if m = 73 then 4513
  else if m = 74 then 4753
  else if m = 75 then 4982
  else if m = 76 then 5089
  else if m = 77 then 5204
  else if m = 78 then 5299
  else if m = 79 then 5408
  else if m = 80 then 5563
  else SqueezeBench.Golomb.Upper.V011.record m

/-- The previous record folded with the table. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V011.record small

end SqueezeBench.Golomb.Upper.V012
