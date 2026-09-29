import SqueezeBench.Problems.Golomb.Records.Upper.V003.Def

/-!
# Golomb upper-bound record V004 — the record function

V003 tabulated the optimal lengths up to `m = 11`; this version continues the table
through `m = 15`, where the Erdős–Turán ruler of V002 is still about three times too long
(`290` against `f(12) = 85`, `481` against `f(15) = 151`). Outside the table the bound
falls back to the previous record, and the two are folded with `minWith`.

Definitions only; validity is proved in `Proof.lean`, where each table entry is witnessed
by the ruler itself.
-/

namespace SqueezeBench.Golomb.Upper.V004

open SqueezeBench

/-- Optimal lengths at the tabulated `m`, the previous record elsewhere. -/
def small (m : ℕ) : ℕ :=
  if m = 12 then 85
  else if m = 13 then 106
  else if m = 14 then 127
  else if m = 15 then 151
  else SqueezeBench.Golomb.Upper.V003.record m

/-- The previous record folded with the table. -/
def record : SqueezeBench.BoundFn := minWith SqueezeBench.Golomb.Upper.V003.record small

end SqueezeBench.Golomb.Upper.V004
