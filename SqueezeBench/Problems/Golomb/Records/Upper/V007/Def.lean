import SqueezeBench.Problems.Golomb.Records.Upper.V006.Def

-- Golomb upper-bound record V007 — the record function.
-- The table of optimal lengths, continued from `m = 18` through `m = 28`, the last `m` at
-- which `f` is known (OEIS A003022; distributed.net OGR-27 and OGR-28). Ruzsa's ruler of V006
-- is still about 1.5× too long there (`341` against `f(18) = 216`, `811` against
-- `f(28) = 585`). Outside the table the bound falls back to the previous record, and the two
-- are folded with `minWith`. Definitions only; validity is proved in `Proof.lean`, where each
-- entry is witnessed by the optimal ruler itself.

namespace SqueezeBench.Golomb.Upper.V007

open SqueezeBench

/-- Optimal lengths at the tabulated `m`, the previous record elsewhere. -/
def small (m : ℕ) : ℕ :=
  if m = 18 then 216
  else if m = 19 then 246
  else if m = 20 then 283
  else if m = 21 then 333
  else if m = 22 then 356
  else if m = 23 then 372
  else if m = 24 then 425
  else if m = 25 then 480
  else if m = 26 then 492
  else if m = 27 then 553
  else if m = 28 then 585
  else SqueezeBench.Golomb.Upper.V006.record m

/-- The previous record folded with the table. -/
def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.Golomb.Upper.V006.record small

end SqueezeBench.Golomb.Upper.V007
