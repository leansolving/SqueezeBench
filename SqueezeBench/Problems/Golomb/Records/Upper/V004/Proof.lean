import SqueezeBench.Problems.Golomb.Records.Upper.V004.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V003.Proof

/-!
# Golomb upper-bound record V004 — validity

Each table entry is an explicit ruler, checked by the kernel: the four conditions of
`RulerLengths` — the marks lie in `range (L+1)`, there are `m` of them, they form a Sidon
set, and `L` is one of them. These are the optimal rulers of OEIS A003022 for
`m = 12, …, 15`; no search happens here, the data is given and only verified.

Outside the table `small` is the previous record, so validity there is V003's.
-/

namespace SqueezeBench.Golomb.Upper.V004

open SqueezeBench

theorem small_valid : UpperBoundHolds f small := by
  intro m
  unfold small
  split_ifs with h12 h13 h14 h15
  · exact h12 ▸ f_le_of_mem (by decide)
      ⟨{0, 2, 6, 24, 29, 40, 43, 55, 68, 75, 76, 85},
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h13 ▸ f_le_of_mem (by decide)
      ⟨{0, 2, 5, 25, 37, 43, 59, 70, 85, 89, 98, 99, 106},
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h14 ▸ f_le_of_mem (by decide)
      ⟨{0, 4, 6, 20, 35, 52, 59, 77, 78, 86, 89, 99, 122, 127},
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h15 ▸ f_le_of_mem (by decide)
      ⟨{0, 4, 20, 30, 57, 59, 62, 76, 100, 111, 123, 136, 144, 145, 151},
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact V003.valid m

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  minWith_valid V003.valid small_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V003.record record :=
  minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V003.record record :=
  minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 12) (by decide) (by decide +kernel)

end SqueezeBench.Golomb.Upper.V004
