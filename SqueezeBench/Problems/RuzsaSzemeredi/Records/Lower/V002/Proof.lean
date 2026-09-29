import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V002.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V001.Proof

/-! Record V002 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the three obligations.
`roth_triple` is Szekeres' tripling step for 3-AP-free sets; iterating it bounds the Roth number
of `[0, m)` below by `2 ^ ⌊log₃ m⌋`, and V001's `key` turns that into triangles. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V002

open SqueezeBench

/-- Szekeres' tripling step: from a 3-AP-free `A ⊆ [0, m)` the set `3A ∪ (3A+1)` is 3-AP-free
in `[0, 3m)` and twice as big. -/
theorem roth_triple (m : ℕ) : 2 * rothNumberNat m ≤ rothNumberNat (3 * m) := by
  classical
  obtain ⟨t, hts, hcard, htf⟩ := rothNumberNat_spec m
  set s : Finset ℕ := t.image (fun a => 3 * a) ∪ t.image (fun a => 3 * a + 1) with hs
  have hmem : ∀ x ∈ s, ∃ y ∈ t, x = 3 * y ∨ x = 3 * y + 1 := by
    intro x hx
    rw [hs, Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨y, hy, Or.inl rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨y, hy, Or.inr rfl⟩
  have hdisj : Disjoint (t.image (fun a => 3 * a)) (t.image (fun a => 3 * a + 1)) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨z, -, hz⟩ := Finset.mem_image.1 hx'
    omega
  have hinj1 : Function.Injective (fun a : ℕ => 3 * a) := by intro a b h; simp only at h; omega
  have hinj2 : Function.Injective (fun a : ℕ => 3 * a + 1) := by
    intro a b h; simp only at h; omega
  have hcards : s.card = 2 * t.card := by
    rw [hs, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
      Finset.card_image_of_injective _ hinj2]
    omega
  have hlt : ∀ x ∈ s, x < 3 * m := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hmem x hx
    have hym : y < m := Finset.mem_range.1 (hts hy)
    omega
  have hsf : ThreeAPFree (s : Set ℕ) := by
    intro a ha b hb c hc habc
    obtain ⟨a', ha', hae⟩ := hmem a ha
    obtain ⟨b', hb', hbe⟩ := hmem b hb
    obtain ⟨c', hc', hce⟩ := hmem c hc
    have E : a' + c' = b' + b' := by
      rcases hae with h1 | h1 <;> rcases hbe with h2 | h2 <;> rcases hce with h3 | h3 <;> omega
    have hab : a' = b' := htf ha' hb' hc' E
    rcases hae with h1 | h1 <;> rcases hbe with h2 | h2 <;> rcases hce with h3 | h3 <;> omega
  have hle := ThreeAPFree.le_rothNumberNat s hsf hlt hcards
  omega

/-- Iterating the tripling step: `2 ^ ⌊log₃ m⌋` is a lower bound for the Roth number. -/
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
          have hfuel : m / 3 ≤ fuel := by omega
          have hih := szAux_le fuel (m / 3) hfuel
          have h2 : 2 * rothNumberNat (m / 3) ≤ rothNumberNat (3 * (m / 3)) := roth_triple _
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
  maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V001.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V001.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V001.record record :=
  maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 57) (by decide) (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V002
