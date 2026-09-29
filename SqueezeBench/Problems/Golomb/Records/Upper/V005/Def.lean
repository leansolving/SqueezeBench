import SqueezeBench.Problems.Golomb.Records.Upper.V004.Def

/-!
# Golomb upper-bound record V005 — the record function

The table of optimal lengths, continued through `m = 17`. The Erdős–Turán ruler of V002
still gives `514` at `m = 16` and `577` at `m = 17`, against the optimal `177` and `199`.
Outside the table the bound falls back to the previous record, and the two are folded with
`minWith`.

Definitions only; validity is proved in `Proof.lean`, where each table entry is witnessed
by the ruler itself.
-/

namespace SqueezeBench.Golomb.Upper.V005

open SqueezeBench

/-- Optimal lengths at the tabulated `m`, the previous record elsewhere. -/
def small (m : ℕ) : ℕ :=
  if m = 16 then 177
  else if m = 17 then 199
  else SqueezeBench.Golomb.Upper.V004.record m

/-- The previous record folded with the table. -/
def record : SqueezeBench.BoundFn := minWith SqueezeBench.Golomb.Upper.V004.record small

end SqueezeBench.Golomb.Upper.V005
