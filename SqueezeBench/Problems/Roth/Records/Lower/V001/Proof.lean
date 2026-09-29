import SqueezeBench.Problems.Roth.Records.Lower.V001.Def
import SqueezeBench.Problems.Roth.Records.Lower.V000.Proof

/-! Record V001 for Roth, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V001.lean`. -/

namespace SqueezeBench.Roth.Lower.V001

open SqueezeBench Finset

-- a singleton is 3-AP-free, so `f n ≥ 1` as soon as the range is nonempty
theorem one_le_f {n : ℕ} (hn : 1 ≤ n) : 1 ≤ SqueezeBench.Roth.f n := by
  refine SqueezeBench.Roth.le_f_of_threeAPFree (by simpa using hn) {0} ?_ ?_ (by simp)
  · intro a ha b hb _ _ _
    simp only [coe_singleton, Set.mem_singleton_iff] at ha hb
    omega
  · intro x hx
    simp only [mem_singleton] at hx
    omega

-- tripling: if `A ⊆ [0, m)` is 3-AP-free then so is `3A ∪ (3A + 1) ⊆ [0, 3m)`
-- a progression there has its three last base-3 digits equal, so dividing by 3 lands back in `A`
theorem two_mul_f_le (m : ℕ) (hm : 1 ≤ m) :
    2 * SqueezeBench.Roth.f m ≤ SqueezeBench.Roth.f (3 * m) := by
  obtain ⟨A, hAsub, hAcard, hAfree⟩ := rothNumberNat_spec m
  have hinj₀ : Function.Injective (fun a : ℕ => 3 * a) := by intro a b h; dsimp only at h; omega
  have hinj₁ : Function.Injective (fun a : ℕ => 3 * a + 1) := by intro a b h; dsimp only at h; omega
  have hdisj : Disjoint (A.image (fun a : ℕ => 3 * a)) (A.image (fun a : ℕ => 3 * a + 1)) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [mem_image] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    omega
  set S : Finset ℕ := A.image (fun a : ℕ => 3 * a) ∪ A.image (fun a : ℕ => 3 * a + 1) with hSdef
  have hmem : ∀ x ∈ S, x / 3 ∈ A ∧ x % 3 ≤ 1 := by
    intro x hx
    simp only [hSdef, mem_union, mem_image] at hx
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have h : 3 * a / 3 = a := by omega
      exact ⟨by rw [h]; exact ha, by omega⟩
    · have h : (3 * a + 1) / 3 = a := by omega
      exact ⟨by rw [h]; exact ha, by omega⟩
  have hcard : S.card = 2 * A.card := by
    rw [hSdef, card_union_of_disjoint hdisj, card_image_of_injective _ hinj₀,
      card_image_of_injective _ hinj₁]
    omega
  have hlt : ∀ x ∈ S, x < 3 * m := by
    intro x hx
    have hx' := (hmem x hx).1
    have hx'' := (hmem x hx).2
    have : x / 3 < m := mem_range.1 (hAsub hx')
    omega
  have hfree : ThreeAPFree (S : Set ℕ) := by
    intro x hx y hy z hz h
    have hx' := hmem x (mem_coe.1 hx)
    have hy' := hmem y (mem_coe.1 hy)
    have hz' := hmem z (mem_coe.1 hz)
    have hdiv : x / 3 + z / 3 = y / 3 + y / 3 := by omega
    have hmod : x % 3 = y % 3 := by omega
    have := hAfree (mem_coe.2 hx'.1) (mem_coe.2 hy'.1) (mem_coe.2 hz'.1) hdiv
    omega
  have hkey : 2 * A.card ≤ SqueezeBench.Roth.f (3 * m) :=
    SqueezeBench.Roth.le_f_of_threeAPFree (by simp; omega) S hfree hlt hcard
  rw [SqueezeBench.Roth.f_of_le hm]
  omega

-- the record's recursion is a valid lower bound as soon as the fuel suffices
theorem szAux_le : ∀ fuel n : ℕ, 1 ≤ n → n ≤ fuel → szAux fuel n ≤ SqueezeBench.Roth.f n := by
  intro fuel
  induction fuel with
  | zero => intro n h1 h2; omega
  | succ fuel ih =>
    intro n h1 h2
    rw [szAux]
    split
    · exact one_le_f h1
    · rename_i hn3
      have hn3' : 3 ≤ n := by omega
      have hle : 2 * SqueezeBench.Roth.f (n / 3) ≤ SqueezeBench.Roth.f (3 * (n / 3)) :=
        two_mul_f_le _ (by omega)
      have hmono : SqueezeBench.Roth.f (3 * (n / 3)) ≤ SqueezeBench.Roth.f n :=
        SqueezeBench.Roth.f_mono (by simp; omega) (by omega)
      have hih := ih (n / 3) (by omega) (by omega)
      omega

theorem szekeres_valid :
    SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f (pin SqueezeBench.Roth.nMin szekeres) :=
  pin_lowerBoundHolds fun n hn => by
    have h1 : 1 ≤ n := by simpa using hn
    exact szAux_le n n h1 le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  maxWith_valid SqueezeBench.Roth.Lower.V000.valid szekeres_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V000.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V000.record record :=
  maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Roth.Lower.V001
