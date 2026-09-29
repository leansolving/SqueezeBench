import SqueezeBench.Problems.Roth.Records.Lower.V002.Def
import SqueezeBench.Problems.Roth.Records.Lower.V001.Proof

/-! Record V002 for Roth, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V002.lean`. -/

namespace SqueezeBench.Roth.Lower.V002

open SqueezeBench Finset

-- `{0, 1}` is 3-AP-free, so `f n ≥ min n 2`
theorem small_le_f {n : ℕ} (hn : n ≤ 2) : n ≤ SqueezeBench.Roth.f n := by
  match n, hn with
  | 0, _ => simp [SqueezeBench.Roth.f]
  | 1, _ => exact SqueezeBench.Roth.Lower.V001.one_le_f le_rfl
  | 2, _ =>
    refine SqueezeBench.Roth.le_f_of_threeAPFree (by simp) {0, 1} ?_ ?_ (by decide)
    · intro a ha b hb c hc h
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
      omega
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      omega

-- splitting on the last base-3 digit: `3 A₁ ∪ (3 A₂ + 1) ⊆ [0, n)` is 3-AP-free
-- a progression there has its three last digits equal, so it lives in one of the two halves
theorem split_le (n : ℕ) (hn : 2 ≤ n) :
    SqueezeBench.Roth.f ((n + 2) / 3) + SqueezeBench.Roth.f ((n + 1) / 3)
      ≤ SqueezeBench.Roth.f n := by
  obtain ⟨A, hAsub, hAcard, hAfree⟩ := rothNumberNat_spec ((n + 2) / 3)
  obtain ⟨B, hBsub, hBcard, hBfree⟩ := rothNumberNat_spec ((n + 1) / 3)
  have hinj₀ : Function.Injective (fun a : ℕ => 3 * a) := by intro a b h; dsimp only at h; omega
  have hinj₁ : Function.Injective (fun a : ℕ => 3 * a + 1) := by
    intro a b h; dsimp only at h; omega
  have hdisj : Disjoint (A.image (fun a : ℕ => 3 * a)) (B.image (fun a : ℕ => 3 * a + 1)) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [mem_image] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    omega
  set S : Finset ℕ := A.image (fun a : ℕ => 3 * a) ∪ B.image (fun a : ℕ => 3 * a + 1) with hSdef
  have hmem : ∀ x ∈ S, x % 3 ≤ 1 ∧ (x % 3 = 0 → x / 3 ∈ A) ∧ (x % 3 = 1 → x / 3 ∈ B) := by
    intro x hx
    simp only [hSdef, mem_union, mem_image] at hx
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have h : 3 * a / 3 = a := by omega
      exact ⟨by omega, fun _ => by rw [h]; exact ha, by omega⟩
    · have h : (3 * a + 1) / 3 = a := by omega
      exact ⟨by omega, by omega, fun _ => by rw [h]; exact ha⟩
  have hcard : S.card = A.card + B.card := by
    rw [hSdef, card_union_of_disjoint hdisj, card_image_of_injective _ hinj₀,
      card_image_of_injective _ hinj₁]
  have hlt : ∀ x ∈ S, x < n := by
    intro x hx
    simp only [hSdef, mem_union, mem_image] at hx
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have : a < (n + 2) / 3 := mem_range.1 (hAsub ha)
      omega
    · have : a < (n + 1) / 3 := mem_range.1 (hBsub ha)
      omega
  have hfree : ThreeAPFree (S : Set ℕ) := by
    intro x hx y hy z hz h
    have hx' := hmem x (mem_coe.1 hx)
    have hy' := hmem y (mem_coe.1 hy)
    have hz' := hmem z (mem_coe.1 hz)
    have hdiv : x / 3 + z / 3 = y / 3 + y / 3 := by omega
    have hmodx : x % 3 = y % 3 := by omega
    have hmodz : z % 3 = y % 3 := by omega
    rcases Nat.lt_or_ge (y % 3) 1 with hy0 | hy1
    · have h0 : y % 3 = 0 := by omega
      have := hAfree (mem_coe.2 (hx'.2.1 (by omega))) (mem_coe.2 (hy'.2.1 h0))
        (mem_coe.2 (hz'.2.1 (by omega))) hdiv
      omega
    · have h1 : y % 3 = 1 := by omega
      have := hBfree (mem_coe.2 (hx'.2.2 (by omega))) (mem_coe.2 (hy'.2.2 h1))
        (mem_coe.2 (hz'.2.2 (by omega))) hdiv
      omega
  have hkey : A.card + B.card ≤ SqueezeBench.Roth.f n :=
    SqueezeBench.Roth.le_f_of_threeAPFree (by simp; omega) S hfree hlt hcard
  rw [SqueezeBench.Roth.f_of_le (show SqueezeBench.Roth.nMin ≤ (n + 2) / 3 by simp; omega),
    SqueezeBench.Roth.f_of_le (show SqueezeBench.Roth.nMin ≤ (n + 1) / 3 by simp; omega)]
  omega

-- the record's recursion is a valid lower bound as soon as the fuel suffices
theorem cntAux_le : ∀ fuel n : ℕ, n ≤ fuel → cntAux fuel n ≤ SqueezeBench.Roth.f n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simp [cntAux, SqueezeBench.Roth.f]
  | succ fuel ih =>
    intro n hn
    rw [cntAux]
    split
    · exact small_le_f (by omega)
    · rename_i h2
      have h3 : 3 ≤ n := by omega
      have h₁ := ih ((n + 2) / 3) (by omega)
      have h₂ := ih ((n + 1) / 3) (by omega)
      have := split_le n (by omega)
      omega

theorem cnt_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f cnt :=
  fun n => cntAux_le n n le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  maxWith_valid SqueezeBench.Roth.Lower.V001.valid cnt_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V001.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V001.record record :=
  maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 14) (by decide) (by decide)

end SqueezeBench.Roth.Lower.V002
