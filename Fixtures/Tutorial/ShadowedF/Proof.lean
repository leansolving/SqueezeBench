import Fixtures.Tutorial.ShadowedF.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

namespace SqueezeBench.Tutorial.Lower.V002
open SqueezeBench SqueezeBench.Tutorial Finset

/-- Mallory's local `f`: twice the truth, so bounding it is strictly easier. -/
def f (m : ℕ) : ℕ := if m < SqueezeBench.Tutorial.nMin then 0 else 2 * SqueezeBench.Tutorial.g m

theorem tutorialF_le (m : ℕ) : SqueezeBench.Tutorial.f m ≤ f m := by
  unfold f SqueezeBench.Tutorial.f
  split
  · exact Nat.le_refl 0
  · omega

theorem oddsBound_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f oddsBound := by
  intro m
  rcases Nat.lt_or_ge m nMin with h | h
  · have hm0 : m = 0 := by simpa using h
    subst hm0; simp [oddsBound, SqueezeBench.Tutorial.f]
  · refine le_f_of_le_g h ?_
    show (m + 1) / 2 ≤ g m
    set k := (m + 1) / 2 with hk
    set S := (range k).image (fun i => 2 * i + 1) with hS
    have hinj : Set.InjOn (fun i => 2 * i + 1) (range k) := by
      intro a _ b _ hab; simp only at hab; omega
    have hcard : S.card = k := by
      rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
    have hsub : S ⊆ Icc 1 m := by
      intro x hx; rw [hS] at hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; simp only [mem_Icc]; omega
    have havoid : AvoidsDoubling S := by
      intro x hx; rw [hS] at hx ⊢
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨i, _, rfl⟩ := hx; rintro ⟨j, _, hEq⟩; omega
    calc k = S.card := hcard.symm
      _ ≤ g m := card_le_g hsub havoid

theorem valid : SqueezeBench.LowerBoundHolds f record :=
  SqueezeBench.maxWith_valid
    (fun m => Nat.le_trans (SqueezeBench.Tutorial.Lower.V001.valid m) (tutorialF_le m))
    (fun m => Nat.le_trans (oddsBound_valid m) (tutorialF_le m))

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Tutorial.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V002
