import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V003.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V002.Proof

/-! Record V003 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the three obligations.
Same tripling recursion as V002 (`V002.roth_triple`), restarted from `r₃(9) ≥ 5` instead of
`r₃(3) ≥ 2`; V001's `key` turns the Roth bound into triangles. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V003

open SqueezeBench

/-- `{0, 1, 3, 7, 8}` contains no nontrivial three-term progression. -/
theorem threeAPFree_five : ThreeAPFree ((({0, 1, 3, 7, 8} : Finset ℕ) : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The Roth number of `[0, m)` is at least `5` once `m ≥ 9`. -/
theorem five_le_rothNumberNat {m : ℕ} (hm : 9 ≤ m) : 5 ≤ rothNumberNat m := by
  have h9 : 5 ≤ rothNumberNat 9 :=
    ThreeAPFree.le_rothNumberNat ({0, 1, 3, 7, 8} : Finset ℕ) threeAPFree_five
      (by intro x hx; simp at hx; omega) (by decide)
  exact le_trans h9 (rothNumberNat.monotone hm)

theorem szAux_le : ∀ fuel m, m ≤ fuel → szAux fuel m ≤ rothNumberNat m
  | 0, m, _ => by simp [szAux]
  | fuel + 1, m, h => by
      rw [szAux]
      split
      · simp
      · rename_i hm0
        split
        · have h1 : min m 2 ≤ rothNumberNat m := V001.min_two_le_rothNumberNat m
          have h2 : 1 ≤ min m 2 := by omega
          omega
        · rename_i hm3
          split
          · have h1 : min m 2 ≤ rothNumberNat m := V001.min_two_le_rothNumberNat m
            have h2 : 2 ≤ min m 2 := by omega
            omega
          · rename_i hm9
            split
            · exact five_le_rothNumberNat (by omega)
            · rename_i hm27
              have hfuel : m / 3 ≤ fuel := by omega
              have hih := szAux_le fuel (m / 3) hfuel
              have h2 : 2 * rothNumberNat (m / 3) ≤ rothNumberNat (3 * (m / 3)) :=
                V002.roth_triple _
              have h3 : rothNumberNat (3 * (m / 3)) ≤ rothNumberNat m :=
                rothNumberNat.monotone (by omega)
              omega

theorem sz_le (m : ℕ) : sz m ≤ rothNumberNat m := szAux_le m m le_rfl

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f v := by
  intro n
  by_cases hn : 3 ≤ n
  · have hle : 6 * V001.blocks n + 3 ≤ n := by unfold V001.blocks; omega
    calc v n = (2 * V001.blocks n + 1) * sz (V001.blocks n) := rfl
      _ ≤ (2 * V001.blocks n + 1) * rothNumberNat (V001.blocks n) :=
          Nat.mul_le_mul_left _ (sz_le _)
      _ ≤ SqueezeBench.RuzsaSzemeredi.f (6 * V001.blocks n + 3) := V001.key _
      _ ≤ SqueezeBench.RuzsaSzemeredi.f n :=
          SqueezeBench.RuzsaSzemeredi.f_mono
            (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]; omega) hle
  · have h0 : V001.blocks n = 0 := by unfold V001.blocks; omega
    simp [v, h0, sz, szAux]

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record :=
  maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V002.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V002.record record :=
  maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 165) (by decide) (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V003
