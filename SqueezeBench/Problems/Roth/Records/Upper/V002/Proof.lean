import SqueezeBench.Problems.Roth.Records.Upper.V002.Def
import SqueezeBench.Problems.Roth.Records.Upper.V001.Proof

/-! Record V002 for Roth, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V002.lean`. -/

namespace SqueezeBench.Roth.Upper.V002

-- Halved sums with a fixed element `u` of a parity class `A` of a 3-AP-free set `S`.
-- They are `|A| - 1` numbers below `n`, none of them in `S`: if `2z = u + a` with `z ∈ S`
-- then `u, z, a` is an arithmetic progression, so `a = u`.
theorem halved_sums (n : ℕ) (S : Finset ℕ) (hlt : ∀ x ∈ S, x < n)
    (hfree : ThreeAPFree (S : Set ℕ)) (A : Finset ℕ) (hAS : A ⊆ S) (r : ℕ)
    (hpar : ∀ x ∈ A, x % 2 = r) (u : ℕ) (huA : u ∈ A) :
    ∃ X : Finset ℕ, X.card = A.card - 1 ∧ X ⊆ Finset.range n ∧ Disjoint S X ∧
      ∀ z ∈ X, ∃ a ∈ A, a ≠ u ∧ 2 * z = u + a := by
  have hun : u < n := hlt u (hAS huA)
  have hupar : u % 2 = r := hpar u huA
  refine ⟨(A.erase u).image (fun a => (u + a) / 2), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem huA]
    intro x hx y hy hxy
    have hx' := hpar x (Finset.mem_of_mem_erase (Finset.mem_coe.mp hx))
    have hy' := hpar y (Finset.mem_of_mem_erase (Finset.mem_coe.mp hy))
    simp only at hxy
    omega
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have han : a < n := hlt a (hAS (Finset.mem_of_mem_erase ha))
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.disjoint_right]
    intro z hz hzS
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have haA := Finset.mem_of_mem_erase ha
    have hane : a ≠ u := Finset.ne_of_mem_erase ha
    have hapar := hpar a haA
    have heq : u + a = (u + a) / 2 + (u + a) / 2 := by omega
    have := hfree (Finset.mem_coe.mpr (hAS huA)) (Finset.mem_coe.mpr hzS)
      (Finset.mem_coe.mpr (hAS haA)) heq
    omega
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have haA := Finset.mem_of_mem_erase ha
    have hapar := hpar a haA
    exact ⟨a, haA, Finset.ne_of_mem_erase ha, by omega⟩

-- The count: `S`, the halved sums with the smallest element of `A` and those with the largest
-- element of `A` are subsets of `{0, …, n-1}` that overlap in at most one point.
theorem key (n : ℕ) (S : Finset ℕ) (hlt : ∀ x ∈ S, x < n) (hfree : ThreeAPFree (S : Set ℕ))
    (A : Finset ℕ) (hAS : A ⊆ S) (r : ℕ) (hpar : ∀ x ∈ A, x % 2 = r) :
    S.card + 2 * A.card ≤ n + 3 := by
  have hSsub : S ⊆ Finset.range n := fun x hx => Finset.mem_range.mpr (hlt x hx)
  have hcardS : S.card ≤ n := by simpa using Finset.card_le_card hSsub
  by_cases hA2 : A.card ≤ 1
  · omega
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hbA : A.min' hAne ∈ A := A.min'_mem hAne
  have hcA : A.max' hAne ∈ A := A.max'_mem hAne
  obtain ⟨X, hXcard, hXsub, hSX, hXrep⟩ :=
    halved_sums n S hlt hfree A hAS r hpar (A.min' hAne) hbA
  obtain ⟨Y, hYcard, hYsub, hSY, hYrep⟩ :=
    halved_sums n S hlt hfree A hAS r hpar (A.max' hAne) hcA
  -- any common point of `X` and `Y` is the halved sum of the two extremes
  have hXY : ∀ z ∈ X, z ∈ Y → 2 * z = A.min' hAne + A.max' hAne := by
    intro z hzX hzY
    obtain ⟨x, hxA, _, hx⟩ := hXrep z hzX
    obtain ⟨y, hyA, _, hy⟩ := hYrep z hzY
    have hxc : x ≤ A.max' hAne := A.le_max' x hxA
    have hyb : A.min' hAne ≤ y := A.min'_le y hyA
    omega
  -- drop that point from `Y` and add up
  have hd : Disjoint (S ∪ X) (Y.erase ((A.min' hAne + A.max' hAne) / 2)) := by
    rw [Finset.disjoint_right]
    intro z hz hzSX
    have hzY : z ∈ Y := Finset.mem_of_mem_erase hz
    have hzne : z ≠ (A.min' hAne + A.max' hAne) / 2 := Finset.ne_of_mem_erase hz
    rcases Finset.mem_union.mp hzSX with h | h
    · exact (Finset.disjoint_right.mp hSY hzY) h
    · exact hzne (by have := hXY z h hzY; omega)
  have hsub : (S ∪ X) ∪ Y.erase ((A.min' hAne + A.max' hAne) / 2) ⊆ Finset.range n :=
    Finset.union_subset (Finset.union_subset hSsub hXsub)
      ((Finset.erase_subset _ _).trans hYsub)
  have htot : ((S ∪ X) ∪ Y.erase ((A.min' hAne + A.max' hAne) / 2)).card ≤ n := by
    simpa using Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hSX] at htot
  have hYe : Y.card - 1 ≤ (Y.erase ((A.min' hAne + A.max' hAne) / 2)).card :=
    Finset.pred_card_le_card_erase
  omega

-- `r₃(n) ≤ (n+3)/2`, by adding the count over the two parity classes.
theorem roth_le (n : ℕ) : rothNumberNat n ≤ (n + 3) / 2 := by
  obtain ⟨t, hts, hcard, hfree⟩ := rothNumberNat_spec n
  have hlt : ∀ x ∈ t, x < n := fun x hx => Finset.mem_range.mp (hts hx)
  have h0 := key n t hlt hfree (t.filter (fun x => x % 2 = 0)) (Finset.filter_subset _ _) 0
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have h1 := key n t hlt hfree (t.filter (fun x => ¬ (x % 2 = 0))) (Finset.filter_subset _ _) 1
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)
  have hsplit : (t.filter (fun x => x % 2 = 0)).card
      + (t.filter (fun x => ¬ (x % 2 = 0))).card = t.card :=
    Finset.card_filter_add_card_filter_not (s := t) (fun x => x % 2 = 0)
  omega

theorem f_le_roth (n : ℕ) : SqueezeBench.Roth.f n ≤ rothNumberNat n := by
  rw [SqueezeBench.Roth.f]
  split
  · exact Nat.zero_le _
  · exact le_rfl

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f v :=
  fun n => le_trans (f_le_roth n) (roth_le n)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V001.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V001.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V001.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 8) (by decide) (by decide)

end SqueezeBench.Roth.Upper.V002
