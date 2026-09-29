import SqueezeBench.Problems.CapSet.Records.Upper.V001.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V000.Proof

/-! Record V001 for CapSet, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V001.lean`. -/

namespace SqueezeBench.CapSet.Upper.V001

open SqueezeBench Finset

variable {m : ℕ}

-- The slice of `A` at last coordinate `t`, pushed down to `Fin m → ZMod 3`.
def slice (A : Finset (Fin (m + 1) → ZMod 3)) (t : ZMod 3) : Finset (Fin m → ZMod 3) :=
  (A.filter (fun a => a (Fin.last m) = t)).image Fin.init

theorem mem_slice {A : Finset (Fin (m + 1) → ZMod 3)} {t : ZMod 3} {x : Fin m → ZMod 3} :
    x ∈ slice A t ↔ (Fin.snoc x t : Fin (m + 1) → ZMod 3) ∈ A := by
  classical
  constructor
  · intro hx
    simp only [slice, mem_image, mem_filter] at hx
    obtain ⟨a, ⟨haA, hal⟩, hax⟩ := hx
    have : (Fin.snoc x t : Fin (m + 1) → ZMod 3) = a := by
      rw [← hax, ← hal, Fin.snoc_init_self]
    rw [this]; exact haA
  · intro hx
    simp only [slice, mem_image, mem_filter]
    exact ⟨Fin.snoc x t, ⟨hx, by simp⟩, by simp⟩

-- The three slices partition `A`.
theorem card_slices (A : Finset (Fin (m + 1) → ZMod 3)) :
    A.card = (slice A 0).card + (slice A 1).card + (slice A 2).card := by
  classical
  have hinj : ∀ t : ZMod 3,
      ((A.filter (fun a => a (Fin.last m) = t)).image Fin.init).card
        = (A.filter (fun a => a (Fin.last m) = t)).card := by
    intro t
    refine card_image_of_injOn ?_
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    rw [← Fin.snoc_init_self a, ← Fin.snoc_init_self b, hab, ha.2, hb.2]
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun a : Fin (m + 1) → ZMod 3 => a (Fin.last m)) (s := A)
    (t := (univ : Finset (ZMod 3))) (fun x _ => mem_univ _)
  rw [hfib, show (univ : Finset (ZMod 3)) = {0, 1, 2} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [slice, hinj, Nat.add_assoc]

-- Three points of `F₃^(m+1)` written as `snoc`s form an arithmetic progression as soon as
-- their two halves do.
theorem snoc_line {x y z : Fin m → ZMod 3} {s t u : ZMod 3}
    (h : x + z = y + y) (h' : s + u = t + t) :
    (Fin.snoc x s : Fin (m + 1) → ZMod 3) + Fin.snoc z u
      = (Fin.snoc y t : Fin (m + 1) → ZMod 3) + Fin.snoc y t := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simpa [Fin.snoc_last] using h'
  · intro j
    simpa [Fin.snoc_castSucc] using congrFun h j

-- Each slice of a cap is a cap one dimension down.
theorem slice_threeAPFree {A : Finset (Fin (m + 1) → ZMod 3)} (t : ZMod 3)
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) :
    ThreeAPFree ((slice A t : Finset (Fin m → ZMod 3)) : Set (Fin m → ZMod 3)) := by
  intro x hx y hy z hz hxyz
  simp only [mem_coe, mem_slice] at hx hy hz
  have := hA (mem_coe.mpr hx) (mem_coe.mpr hy) (mem_coe.mpr hz) (snoc_line hxyz rfl)
  calc x = Fin.init (Fin.snoc x t : Fin (m + 1) → ZMod 3) := by simp
    _ = Fin.init (Fin.snoc y t : Fin (m + 1) → ZMod 3) := by rw [this]
    _ = y := by simp

-- If the slice at `2` is nonempty, the slices at `0` and `1` together fit inside `F₃^m`:
-- translating the slice at `0` by a point `z` of the slice at `2` lands in the complement
-- of the slice at `1`, since `(x,0), (-(x+z),1), (z,2)` is a line.
theorem card_slice_zero_add_one {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) {z : Fin m → ZMod 3}
    (hz : z ∈ slice A 2) :
    (slice A 0).card + (slice A 1).card ≤ 3 ^ m := by
  classical
  have hdbl : ∀ v : ZMod 3, -v + -v = v := by decide
  have hsub : (slice A 0).image (fun x => -(x + z))
      ⊆ (univ : Finset (Fin m → ZMod 3)) \ slice A 1 := by
    intro w hw
    simp only [mem_image] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [mem_sdiff]
    refine ⟨mem_univ _, ?_⟩
    intro hmem
    rw [mem_slice] at hx hz hmem
    have hline : x + z = -(x + z) + -(x + z) := by
      funext i; simpa using (hdbl (x i + z i)).symm
    have := hA (mem_coe.mpr hx) (mem_coe.mpr hmem) (mem_coe.mpr hz)
      (snoc_line hline (by decide))
    have h01 := congrFun this (Fin.last m)
    simp only [Fin.snoc_last] at h01
    exact absurd h01 (by decide)
  have hcard : ((slice A 0).image (fun x => -(x + z))).card = (slice A 0).card := by
    refine card_image_of_injective _ ?_
    intro a b hab
    simpa using hab
  have h1 := card_le_card hsub
  rw [hcard] at h1
  have h2 := Finset.card_sdiff_add_card_eq_card (subset_univ (slice A 1))
  have h3 : (univ : Finset (Fin m → ZMod 3)).card = 3 ^ m := by simp
  omega

-- The recurrence: a cap in `F₃^(m+1)` has at most `3^m + B` points whenever every cap in
-- `F₃^m` has at most `B` points.
theorem step {B : ℕ}
    (hB : ∀ S : Finset (Fin m → ZMod 3), ThreeAPFree (S : Set (Fin m → ZMod 3)) → S.card ≤ B)
    {A : Finset (Fin (m + 1) → ZMod 3)} (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) :
    A.card ≤ 3 ^ m + B := by
  classical
  have hsum := card_slices A
  have h3 : (univ : Finset (Fin m → ZMod 3)).card = 3 ^ m := by simp
  rcases Finset.eq_empty_or_nonempty (slice A 2) with h2 | ⟨z, hz⟩
  · have hA0 : (slice A 0).card ≤ 3 ^ m := by
      have := card_le_card (subset_univ (slice A 0)); omega
    have hA1 : (slice A 1).card ≤ B := hB _ (slice_threeAPFree 1 hA)
    rw [h2] at hsum
    simp only [card_empty, Nat.add_zero] at hsum
    omega
  · have h01 := card_slice_zero_add_one hA hz
    have hA2 : (slice A 2).card ≤ B := hB _ (slice_threeAPFree 2 hA)
    omega

-- Unrolling the recurrence from `f 1 ≤ 2`.
theorem cap_card_le : ∀ m : ℕ, ∀ A : Finset (Fin (m + 1) → ZMod 3),
    ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3)) → A.card ≤ (3 ^ (m + 1) + 1) / 2 := by
  intro m
  induction m with
  | zero =>
    intro A hA
    have h := SqueezeBench.CapSet.Upper.V000.card_le_of_threeAPFree hA
    norm_num at h ⊢
    exact h
  | succ k ih =>
    intro A hA
    have h := step (B := (3 ^ (k + 1) + 1) / 2) (fun S hS => ih S hS) hA
    have hp : 3 ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by ring
    omega

theorem f_le (n : ℕ) : SqueezeBench.CapSet.f n ≤ (3 ^ n + 1) / 2 := by
  match n with
  | 0 => simp [SqueezeBench.CapSet.f, SqueezeBench.CapSet.nMin]
  | m + 1 =>
    have hn : SqueezeBench.CapSet.nMin ≤ m + 1 := by simp [SqueezeBench.CapSet.nMin]
    have hlt : SqueezeBench.CapSet.f (m + 1) < (3 ^ (m + 1) + 1) / 2 + 1 := by
      refine SqueezeBench.CapSet.f_lt_of_forall_not hn ?_
      intro A hA hAPF
      simp only [mem_powersetCard_univ] at hA
      have := cap_card_le m A hAPF
      omega
    omega

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record := fun n => f_le n

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V000.record record := by
  intro n
  match n with
  | 0 => simp [record, SqueezeBench.CapSet.Upper.V000.record]
  | m + 1 =>
    have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
    simp only [record, SqueezeBench.CapSet.Upper.V000.record, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V000.record record :=
  ⟨2, by simp [SqueezeBench.CapSet.nMin], by
    simp only [record, SqueezeBench.CapSet.Upper.V000.record]
    norm_num⟩

end SqueezeBench.CapSet.Upper.V001
