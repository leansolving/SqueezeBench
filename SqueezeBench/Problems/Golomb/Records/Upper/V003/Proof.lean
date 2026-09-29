import SqueezeBench.Problems.Golomb.Records.Upper.V003.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V002.Proof

/-!
# Golomb upper-bound record V003 — validity

Each table entry is an explicit ruler, checked by the kernel: the four conditions of
`RulerLengths` — the marks lie in `range (L+1)`, there are `m` of them, they form a Sidon
set, and `L` is one of them. These are the optimal rulers of OEIS A003022 for
`m = 4, 7, 8, 9, 10, 11`; no search happens here, the data is given and only
verified.

Outside the table `small` is the previous record, so validity there is V002's.
-/

namespace SqueezeBench.Golomb.Upper.V003

open SqueezeBench

theorem small_valid : UpperBoundHolds f small := by
  intro m
  unfold small
  split_ifs with h4 h7 h8 h9 h10 h11
  · exact h4 ▸ f_le_of_mem (by decide) ⟨{0, 1, 4, 6}, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h7 ▸ f_le_of_mem (by decide)
      ⟨{0, 1, 4, 10, 18, 23, 25}, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h8 ▸ f_le_of_mem (by decide)
      ⟨{0, 1, 4, 9, 15, 22, 32, 34}, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h9 ▸ f_le_of_mem (by decide)
      ⟨{0, 1, 5, 12, 25, 27, 35, 41, 44}, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h10 ▸ f_le_of_mem (by decide)
      ⟨{0, 1, 6, 10, 23, 26, 34, 41, 53, 55}, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h11 ▸ f_le_of_mem (by decide)
      ⟨{0, 1, 4, 13, 28, 33, 47, 54, 64, 70, 72}, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact V002.valid m

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  minWith_valid V002.valid small_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V002.record record :=
  minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V002.record record :=
  minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 10) (by decide) (by decide +kernel)

end SqueezeBench.Golomb.Upper.V003
