import SqueezeBench.Problems.Golomb.Records.Upper.V002.Def

/-!
# Golomb upper-bound record V003 — the record function

A table of explicit optimal rulers for `m = 4` and `m = 7, …, 11`, where the general
constructions are still far off: `f(7) = 25` against the binary ruler's `63`, `f(11) = 72`
against the Erdős–Turán ruler's `269`. Outside the table the bound falls back to the
previous record, and the two are folded with `minWith`.

Definitions only; validity is proved in `Proof.lean`, where each table entry is witnessed
by the ruler itself.
-/

namespace SqueezeBench.Golomb.Upper.V003

open SqueezeBench

/-- Optimal lengths at the tabulated `m`, the previous record elsewhere. -/
def small (m : ℕ) : ℕ :=
  if m = 4 then 6
  else if m = 7 then 25
  else if m = 8 then 34
  else if m = 9 then 44
  else if m = 10 then 55
  else if m = 11 then 72
  else SqueezeBench.Golomb.Upper.V002.record m

/-- The previous record folded with the table. -/
def record : SqueezeBench.BoundFn := minWith SqueezeBench.Golomb.Upper.V002.record small

end SqueezeBench.Golomb.Upper.V003
