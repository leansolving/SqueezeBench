import SqueezeBench.Problems.Roth.Records.Upper.V003.Def
import SqueezeBench.Problems.Roth.Records.Upper.V002.Proof

/-! Record V003 for Roth, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Upper/V003.lean`. -/

namespace SqueezeBench.Roth.Upper.V003

-- The arithmetic heart. `V002.key` gives `k + 2 * e ≤ n + 3` for each of the two parity
-- classes of a 3-AP-free `S ⊆ [0, n)`, with `e₀ + e₁ = k`. V002 averages the two, which loses
-- the integrality: the average is attained only at `e₀ = e₁ = k / 2`, impossible for odd `k`.
-- Splitting on the parity of `k` and on which class is the larger keeps it: the larger class
-- has `e ≥ ⌈k / 2⌉`, so `k` odd forces `2 * k ≤ n + 2`, one better than `2 * k ≤ n + 3`.
theorem arith {n k e₀ e₁ : ℕ} (h₀ : k + 2 * e₀ ≤ n + 3) (h₁ : k + 2 * e₁ ≤ n + 3)
    (hs : e₀ + e₁ = k) : k ≤ v n := by
  rw [v]
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩ <;>
    rcases le_total e₁ e₀ with h | h <;> omega

-- `r₃(n) ≤ v n`, by applying the V002 count to both parity classes and keeping the integrality.
theorem roth_le (n : ℕ) : rothNumberNat n ≤ v n := by
  obtain ⟨t, hts, hcard, hfree⟩ := rothNumberNat_spec n
  have hlt : ∀ x ∈ t, x < n := fun x hx => Finset.mem_range.mp (hts hx)
  have h₀ := SqueezeBench.Roth.Upper.V002.key n t hlt hfree
    (t.filter (fun x => x % 2 = 0)) (Finset.filter_subset _ _) 0
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have h₁ := SqueezeBench.Roth.Upper.V002.key n t hlt hfree
    (t.filter (fun x => ¬ (x % 2 = 0))) (Finset.filter_subset _ _) 1
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; omega)
  have hsplit : (t.filter (fun x => x % 2 = 0)).card
      + (t.filter (fun x => ¬ (x % 2 = 0))).card = t.card :=
    Finset.card_filter_add_card_filter_not (s := t) (fun x => x % 2 = 0)
  rw [← hcard]
  exact arith h₀ h₁ hsplit

theorem f_le_roth (n : ℕ) : SqueezeBench.Roth.f n ≤ rothNumberNat n := by
  rw [SqueezeBench.Roth.f]
  split
  · exact Nat.zero_le _
  · exact le_rfl

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f v :=
  fun n => le_trans (f_le_roth n) (roth_le n)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Roth.Upper.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Roth.Upper.V002.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Roth.nMin SqueezeBench.Roth.Upper.V002.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 7) (by decide) (by decide)

end SqueezeBench.Roth.Upper.V003
