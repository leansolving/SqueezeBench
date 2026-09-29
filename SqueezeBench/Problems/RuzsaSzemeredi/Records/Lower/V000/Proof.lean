import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V000.Def

/-!
# Ruzsa–Szemerédi lower-bound record V000 — validity

`K₃` is locally linear and has one triangle; both facts are concrete enough for `decide`.
Monotonicity carries the bound to every `n ≥ 3`.
-/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V000

open SqueezeBench

theorem valid : LowerBoundHolds f record := pin_lowerBoundHolds fun _ hn => one_le_f hn

end SqueezeBench.RuzsaSzemeredi.Lower.V000
