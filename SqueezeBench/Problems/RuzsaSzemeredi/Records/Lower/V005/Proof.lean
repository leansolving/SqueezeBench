import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V005.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V004.Proof

/-! Record V005 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the three obligations.
Each entry of `base` is backed by an explicit 3-AP-free set: being 3-AP-free is a finite check on
the elements of the set, so `decide` settles it without any search. V004's `roth_split` then lets
the recursion take the better of the table and the split at every level, and V001's `key` turns
the resulting Roth bound into triangles. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V005

open SqueezeBench

/-- 3-AP-freeness of a `Finset` is the finite statement about its own elements. -/
theorem apFree_of {s : Finset ℕ} (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = b + b → a = b) :
    ThreeAPFree (s : Set ℕ) := by
  intro a ha b hb c hc habc
  exact h a (by simpa using ha) b (by simpa using hb) c (by simpa using hc) habc

/-- An explicit 3-AP-free subset of `[0, M)` of size `k` bounds the Roth number of `[0, M)`. -/
theorem le_roth_of {s : Finset ℕ} {M k : ℕ}
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = b + b → a = b) (hlt : ∀ x ∈ s, x < M)
    (hc : s.card = k) : k ≤ rothNumberNat M :=
  ThreeAPFree.le_rothNumberNat s (apFree_of h) hlt hc

theorem r9 : 5 ≤ rothNumberNat 9 := V003.five_le_rothNumberNat (le_refl 9)

theorem r11 : 6 ≤ rothNumberNat 11 :=
  le_roth_of (s := {0, 1, 3, 4, 9, 10}) (by decide) (by decide) (by decide)

theorem r20 : 9 ≤ rothNumberNat 20 :=
  le_roth_of (s := {0, 1, 5, 6, 8, 13, 14, 17, 19}) (by decide) (by decide) (by decide)

theorem r24 : 10 ≤ rothNumberNat 24 :=
  le_roth_of (s := {0, 1, 4, 6, 10, 15, 17, 18, 22, 23}) (by decide) (by decide) (by decide)

theorem r26 : 11 ≤ rothNumberNat 26 :=
  le_roth_of (s := {0, 1, 4, 6, 10, 15, 17, 18, 22, 23, 25}) (by decide) (by decide) (by decide)

theorem r30 : 12 ≤ rothNumberNat 30 :=
  le_roth_of (s := {0, 2, 3, 7, 8, 10, 19, 21, 22, 26, 27, 29}) (by decide) (by decide) (by decide)

theorem r32 : 13 ≤ rothNumberNat 32 :=
  le_roth_of (s := {0, 1, 3, 7, 8, 10, 18, 21, 22, 25, 27, 30, 31}) (by decide) (by decide)
    (by decide)

theorem r36 : 14 ≤ rothNumberNat 36 :=
  le_roth_of (s := {0, 1, 3, 7, 8, 12, 20, 22, 25, 26, 29, 31, 34, 35}) (by decide) (by decide)
    (by decide)

/-- Every entry of the table is a lower bound for the Roth number, by monotonicity. -/
theorem base_le (m : ℕ) : base m ≤ rothNumberNat m := by
  have mono : ∀ {M k : ℕ}, k ≤ rothNumberNat M → M ≤ m → k ≤ rothNumberNat m :=
    fun h hM => le_trans h (rothNumberNat.monotone hM)
  unfold base
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact Nat.zero_le _
  · exact mono r9 (by omega)
  · exact mono r11 (by omega)
  · exact mono r20 (by omega)
  · exact mono r24 (by omega)
  · exact mono r26 (by omega)
  · exact mono r30 (by omega)
  · exact mono r32 (by omega)
  · exact mono r36 (by omega)

theorem szAux_le : ∀ fuel m, m ≤ fuel → szAux fuel m ≤ rothNumberNat m
  | 0, m, _ => by simp [szAux]
  | fuel + 1, m, h => by
      rw [szAux]
      split
      · have h1 := V001.min_two_le_rothNumberNat m
        omega
      · rename_i hm2
        have hb := base_le m
        have hf1 : (m + 2) / 3 ≤ fuel := by omega
        have hf2 : (m + 1) / 3 ≤ fuel := by omega
        have ih1 := szAux_le fuel ((m + 2) / 3) hf1
        have ih2 := szAux_le fuel ((m + 1) / 3) hf2
        have hsplit := V004.roth_split m
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
  maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V004.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V004.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V004.record record :=
  maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 195) (by decide) (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V005
