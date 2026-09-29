import SqueezeBench.Problems.Golomb.Records.Upper.V005.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V004.Proof

/-!
# Golomb upper-bound record V005 — validity

Each table entry is an explicit ruler, checked by the kernel: the four conditions of
`RulerLengths` — the marks lie in `range (L+1)`, there are `m` of them, they form a Sidon
set, and `L` is one of them. These are the optimal rulers of OEIS A003022 for
`m = 16, 17`; no search happens here, the data is given and only verified.

Outside the table `small` is the previous record, so validity there is V004's.
-/

namespace SqueezeBench.Golomb.Upper.V005

open SqueezeBench

theorem small_valid : UpperBoundHolds f small := by
  intro m
  unfold small
  split_ifs with h16 h17
  · exact h16 ▸ f_le_of_mem (by decide)
      ⟨{0, 1, 4, 11, 26, 32, 56, 68, 76, 115, 117, 134, 150, 163, 168, 177},
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact h17 ▸ f_le_of_mem (by decide)
      ⟨{0, 5, 7, 17, 52, 56, 67, 80, 81, 100, 122, 138, 159, 165, 168, 191, 199},
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact V004.valid m

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  minWith_valid V004.valid small_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V004.record record :=
  minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V004.record record :=
  minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 16) (by decide) (by decide +kernel)

end SqueezeBench.Golomb.Upper.V005
