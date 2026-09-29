import Fixtures.Tutorial.SplitSearch.Def
import SqueezeBench.Problems.Tutorial.Records.Lower.V001.Proof

namespace SqueezeBench.Tutorial.Lower.V002

open SqueezeBench SqueezeBench.Tutorial Finset

-- a search split into 50 lemmas: each is far within 200000 heartbeats, together they exceed it
def loop : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => loop n ((a * 31 + n) % 1000003)

theorem chunk0 : loop 20000 0 = 285785 := by decide +kernel
theorem chunk1 : loop 20000 1 = 608783 := by decide +kernel
theorem chunk2 : loop 20000 2 = 931781 := by decide +kernel
theorem chunk3 : loop 20000 3 = 254776 := by decide +kernel
theorem chunk4 : loop 20000 4 = 577774 := by decide +kernel
theorem chunk5 : loop 20000 5 = 900772 := by decide +kernel
theorem chunk6 : loop 20000 6 = 223767 := by decide +kernel
theorem chunk7 : loop 20000 7 = 546765 := by decide +kernel
theorem chunk8 : loop 20000 8 = 869763 := by decide +kernel
theorem chunk9 : loop 20000 9 = 192758 := by decide +kernel
theorem chunk10 : loop 20000 10 = 515756 := by decide +kernel
theorem chunk11 : loop 20000 11 = 838754 := by decide +kernel
theorem chunk12 : loop 20000 12 = 161749 := by decide +kernel
theorem chunk13 : loop 20000 13 = 484747 := by decide +kernel
theorem chunk14 : loop 20000 14 = 807745 := by decide +kernel
theorem chunk15 : loop 20000 15 = 130740 := by decide +kernel
theorem chunk16 : loop 20000 16 = 453738 := by decide +kernel
theorem chunk17 : loop 20000 17 = 776736 := by decide +kernel
theorem chunk18 : loop 20000 18 = 99731 := by decide +kernel
theorem chunk19 : loop 20000 19 = 422729 := by decide +kernel
theorem chunk20 : loop 20000 20 = 745727 := by decide +kernel
theorem chunk21 : loop 20000 21 = 68722 := by decide +kernel
theorem chunk22 : loop 20000 22 = 391720 := by decide +kernel
theorem chunk23 : loop 20000 23 = 714718 := by decide +kernel
theorem chunk24 : loop 20000 24 = 37713 := by decide +kernel
theorem chunk25 : loop 20000 25 = 360711 := by decide +kernel
theorem chunk26 : loop 20000 26 = 683709 := by decide +kernel
theorem chunk27 : loop 20000 27 = 6704 := by decide +kernel
theorem chunk28 : loop 20000 28 = 329702 := by decide +kernel
theorem chunk29 : loop 20000 29 = 652700 := by decide +kernel
theorem chunk30 : loop 20000 30 = 975698 := by decide +kernel
theorem chunk31 : loop 20000 31 = 298693 := by decide +kernel
theorem chunk32 : loop 20000 32 = 621691 := by decide +kernel
theorem chunk33 : loop 20000 33 = 944689 := by decide +kernel
theorem chunk34 : loop 20000 34 = 267684 := by decide +kernel
theorem chunk35 : loop 20000 35 = 590682 := by decide +kernel
theorem chunk36 : loop 20000 36 = 913680 := by decide +kernel
theorem chunk37 : loop 20000 37 = 236675 := by decide +kernel
theorem chunk38 : loop 20000 38 = 559673 := by decide +kernel
theorem chunk39 : loop 20000 39 = 882671 := by decide +kernel
theorem chunk40 : loop 20000 40 = 205666 := by decide +kernel
theorem chunk41 : loop 20000 41 = 528664 := by decide +kernel
theorem chunk42 : loop 20000 42 = 851662 := by decide +kernel
theorem chunk43 : loop 20000 43 = 174657 := by decide +kernel
theorem chunk44 : loop 20000 44 = 497655 := by decide +kernel
theorem chunk45 : loop 20000 45 = 820653 := by decide +kernel
theorem chunk46 : loop 20000 46 = 143648 := by decide +kernel
theorem chunk47 : loop 20000 47 = 466646 := by decide +kernel
theorem chunk48 : loop 20000 48 = 789644 := by decide +kernel
theorem chunk49 : loop 20000 49 = 112639 := by decide +kernel

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

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Tutorial.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Tutorial.Lower.V001.valid oddsBound_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Tutorial.nMin SqueezeBench.Tutorial.Lower.V001.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Tutorial.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Tutorial.Lower.V002
