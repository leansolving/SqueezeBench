import SqueezeBench.Problems.CapSet.Records.Upper.V000.Def

/-!
# CapSet upper-bound record V000 — validity
-/

namespace SqueezeBench.CapSet.Upper.V000

open SqueezeBench Finset

theorem card_le_of_threeAPFree {m : ℕ} {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) : A.card ≤ 2 * 3 ^ m := by
  classical
  have hvals : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hfib : ∀ b ∈ A.image Fin.init, {a ∈ A | Fin.init a = b}.card ≤ 2 := by
    intro b _
    by_contra hlt
    rw [Nat.not_le] at hlt
    set e0 : Fin (m + 1) → ZMod 3 := Fin.snoc b 0 with he0
    set e1 : Fin (m + 1) → ZMod 3 := Fin.snoc b 1 with he1
    set e2 : Fin (m + 1) → ZMod 3 := Fin.snoc b 2 with he2
    have hsub : {a ∈ A | Fin.init a = b} ⊆ ({e0, e1, e2} : Finset _) := by
      intro a ha
      simp only [mem_filter] at ha
      have hre : (Fin.snoc (Fin.init a) (a (Fin.last m)) : Fin (m + 1) → ZMod 3) = a :=
        Fin.snoc_init_self a
      rw [ha.2] at hre
      rcases hvals (a (Fin.last m)) with h | h | h <;> rw [h] at hre <;>
        simp [← hre, he0, he1, he2]
    have hTcard : ({e0, e1, e2} : Finset (Fin (m + 1) → ZMod 3)).card ≤ 3 := by
      refine (card_insert_le _ _).trans ?_
      have := card_insert_le e1 ({e2} : Finset (Fin (m + 1) → ZMod 3))
      simp only [card_singleton] at this
      omega
    have heq : {a ∈ A | Fin.init a = b} = ({e0, e1, e2} : Finset _) :=
      eq_of_subset_of_card_le hsub (by omega)
    have hmem : ∀ e ∈ ({e0, e1, e2} : Finset (Fin (m + 1) → ZMod 3)), e ∈ A := by
      intro e he
      rw [← heq] at he
      exact (mem_filter.mp he).1
    have hline : e0 + e2 = e1 + e1 := by
      funext i
      simp only [Pi.add_apply, he0, he1, he2]
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; decide
      · intro j; simp only [Fin.snoc_castSucc]
    have hkey := hA (mem_coe.mpr (hmem e0 (by simp))) (mem_coe.mpr (hmem e1 (by simp)))
      (mem_coe.mpr (hmem e2 (by simp))) hline
    have hcon : (0 : ZMod 3) = 1 := by
      have h := congrFun hkey (Fin.last m)
      simp only [he0, he1, Fin.snoc_last] at h
      exact h
    exact absurd hcon (by decide)
  have h1 := Finset.card_le_mul_card_image (f := Fin.init) A 2 hfib
  have h2 : (A.image (Fin.init : (Fin (m + 1) → ZMod 3) → (Fin m → ZMod 3))).card ≤ 3 ^ m := by
    calc (A.image Fin.init).card ≤ (univ : Finset (Fin m → ZMod 3)).card := card_le_univ _
      _ = 3 ^ m := by simp
  omega

theorem valid : UpperBoundHolds f record := by
  intro n
  match n with
  | 0 => simp [record, f, nMin]
  | m + 1 =>
    have hn : nMin ≤ m + 1 := by simp [nMin]
    have hlt : f (m + 1) < 2 * 3 ^ m + 1 := by
      refine f_lt_of_forall_not hn ?_
      intro A hA hAPF
      simp only [mem_powersetCard_univ] at hA
      have := card_le_of_threeAPFree hAPF
      omega
    have hu : record (m + 1) = 2 * 3 ^ m := by simp [record]
    omega

end SqueezeBench.CapSet.Upper.V000
