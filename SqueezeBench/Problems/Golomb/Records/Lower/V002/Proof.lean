import SqueezeBench.Problems.Golomb.Records.Lower.V002.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V001.Proof

/-!
# Golomb lower-bound record V002 — validity

Nothing new is needed: V001's `master` inequality is stated for every threshold `q` and
every window length, so every `bnd m q u` is a lower bound on every achievable length.
The record is the maximum of twelve of them, and `max_le` discharges it.
-/

namespace SqueezeBench.Golomb.Lower.V002

open SqueezeBench Finset

/-- Every pair `(q, u)` gives a lower bound on every achievable length. -/
theorem bnd_le {m L : ℕ} (hL : L ∈ RulerLengths m) (q u : ℕ) : bnd m q u ≤ L := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp [bnd]
  rcases Nat.eq_zero_or_pos u with hu | hu
  · subst hu; simp [bnd]
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  have hqq : 0 < q * (q + 1) := Nat.mul_pos hq (by omega)
  have hmas := SqueezeBench.Golomb.Lower.V001.master hL q v
  have key : 2 * q * (v + 1) * m - v * (v + 1) ≤ (L + v + 1) * (q * (q + 1)) := by omega
  have h1 := SqueezeBench.Golomb.Lower.V001.div_le_of_mul_le hqq key
  have h2 : bnd m q (v + 1)
      = (2 * q * (v + 1) * m - v * (v + 1)) / (q * (q + 1)) - (v + 1) := by
    rw [bnd]
    simp only [Nat.add_sub_cancel]
  rw [h2]
  omega

theorem w_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f w := by
  refine pin_lowerBoundHolds ?_
  intro m hm
  refine le_f hm ?_
  intro L hL
  show wRaw m ≤ L
  simp only [wRaw, bestU]
  repeat' apply max_le
  all_goals exact bnd_le hL _ _

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  maxWith_valid SqueezeBench.Golomb.Lower.V001.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V001.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V001.record record :=
  maxWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Golomb.Lower.V002
