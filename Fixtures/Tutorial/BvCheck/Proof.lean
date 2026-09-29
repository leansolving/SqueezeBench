import Std.Tactic.BVDecide
import Fixtures.Tutorial.BvCheck.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

namespace SqueezeBench.Tutorial.Lower.V002

open SqueezeBench SqueezeBench.Tutorial Finset

-- A bit-vector identity beyond `bv_normalize`, established by a SAT certificate.
theorem bvFact : ∀ a b : BitVec 8, (a &&& b) + (a ||| b) = a + b := by
  bv_check (config := { binaryProofs := false }) "bvFact.lrat"

theorem oddsBound_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f oddsBound := by
  intro m
  rcases Nat.lt_or_ge m nMin with h | h
  · have hm0 : m = 0 := by simpa using h
    subst hm0
    simp [oddsBound, f]
  · refine le_f_of_le_g h ?_
    show (m + 1) / 2 ≤ g m
    set k := (m + 1) / 2 with hk
    set S := (range k).image (fun i => 2 * i + 1) with hS
    have hinj : Set.InjOn (fun i => 2 * i + 1) (range k) := by
      intro a _ b _ hab
      simp only at hab
      omega
    have hcard : S.card = k := by
      rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
    have hsub : S ⊆ Icc 1 m := by
      intro x hx
      rw [hS] at hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [mem_Icc]
      omega
    have havoid : AvoidsDoubling S := by
      intro x hx
      rw [hS] at hx ⊢
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨i, _, rfl⟩ := hx
      rintro ⟨j, _, hEq⟩
      omega
    calc k = S.card := hcard.symm
      _ ≤ g m := card_le_g hsub havoid

-- `have` keeps `bvFact` in the proof term, so its axiom is in the closure of `valid`.
theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record := by
  have _h := bvFact 0 0
  exact SqueezeBench.maxWith_valid SqueezeBench.Tutorial.Lower.V001.valid oddsBound_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Tutorial.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V002
