import SqueezeBench.Problems.Roth.Records.Upper.V001.Def
import SqueezeBench.Problems.Roth.Records.Upper.V000.Proof

/-! Record V001 for Roth, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V001.lean`. -/

namespace SqueezeBench.Roth.Upper.V001

-- `f` is `rothNumberNat` above `nMin` and `0` below it, so it never exceeds `rothNumberNat`.
theorem f_le_roth (n : ℕ) : SqueezeBench.Roth.f n ≤ rothNumberNat n := by
  rw [SqueezeBench.Roth.f]
  split
  · exact Nat.zero_le _
  · exact le_rfl

-- `{0, 1, 2}` is an arithmetic progression, so it is the only 3-subset of `range 3` and it is
-- not 3-AP-free.
theorem roth_three : rothNumberNat 3 ≤ 2 := by
  by_contra hcon
  obtain ⟨t, hts, hcard, hfree⟩ := rothNumberNat_spec 3
  have hle : rothNumberNat 3 ≤ 3 := rothNumberNat_le 3
  have h3 : t.card = 3 := by omega
  have ht : t = Finset.range 3 := Finset.eq_of_subset_of_card_le hts (by simp [h3])
  subst ht
  have h0 : (0 : ℕ) ∈ ((Finset.range 3 : Finset ℕ) : Set ℕ) := by simp
  have h1 : (1 : ℕ) ∈ ((Finset.range 3 : Finset ℕ) : Set ℕ) := by simp
  have h2 : (2 : ℕ) ∈ ((Finset.range 3 : Finset ℕ) : Set ℕ) := by simp
  exact absurd (hfree h0 h1 h2 (by norm_num)) (by norm_num)

-- Subadditivity of the Roth number, `k` blocks of three at a time.
theorem roth_block (k : ℕ) : rothNumberNat (3 * k) ≤ 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit : 3 * (k + 1) = 3 * k + 3 := by ring
      rw [hsplit]
      calc rothNumberNat (3 * k + 3) ≤ rothNumberNat (3 * k) + rothNumberNat 3 :=
            rothNumberNat_add_le _ _
        _ ≤ 2 * k + 2 := Nat.add_le_add ih roth_three
        _ = 2 * (k + 1) := by ring

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f v := by
  intro n
  have hmono : rothNumberNat n ≤ rothNumberNat (3 * ((n + 2) / 3)) :=
    rothNumberNat.monotone (by omega)
  exact le_trans (f_le_roth n) (le_trans hmono (roth_block _))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V000.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V000.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 3) (by decide) (by decide)

end SqueezeBench.Roth.Upper.V001
