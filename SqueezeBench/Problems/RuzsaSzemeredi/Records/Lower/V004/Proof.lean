import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V004.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V003.Proof

/-! Record V004 for RuzsaSzemeredi, lower direction, by baseline claude-opus-5: the three obligations.
`roth_split` sharpens V002's `roth_triple`: the two residue classes kept by the Szekeres step may
come from *different* 3-AP-free sets, so `r₃(m) ≥ r₃(⌈m/3⌉) + r₃(⌈(m-1)/3⌉)`. Iterating it from
the base values of V001 and V003 gives `sz`, and V001's `key` turns it into triangles. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V004

open SqueezeBench

/-- The split step: if `A ⊆ [0, ⌈m/3⌉)` and `B ⊆ [0, ⌈(m-1)/3⌉)` are 3-AP-free then so is
`3A ∪ (3B+1) ⊆ [0, m)`. A progression inside the union cannot mix the two residue classes,
since `a + c = 2b` forces the three residues mod `3` to agree. -/
theorem roth_split (m : ℕ) :
    rothNumberNat ((m + 2) / 3) + rothNumberNat ((m + 1) / 3) ≤ rothNumberNat m := by
  classical
  obtain ⟨t, hts, hcardt, htf⟩ := rothNumberNat_spec ((m + 2) / 3)
  obtain ⟨u, hus, hcardu, huf⟩ := rothNumberNat_spec ((m + 1) / 3)
  set s : Finset ℕ := t.image (fun a => 3 * a) ∪ u.image (fun a => 3 * a + 1) with hs
  have hmem : ∀ x ∈ s, (∃ y ∈ t, x = 3 * y) ∨ (∃ y ∈ u, x = 3 * y + 1) := by
    intro x hx
    rw [hs, Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact Or.inl ⟨y, hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact Or.inr ⟨y, hy, rfl⟩
  have hdisj : Disjoint (t.image (fun a => 3 * a)) (u.image (fun a => 3 * a + 1)) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨z, -, hz⟩ := Finset.mem_image.1 hx'
    omega
  have hinj1 : Function.Injective (fun a : ℕ => 3 * a) := by intro a b h; simp only at h; omega
  have hinj2 : Function.Injective (fun a : ℕ => 3 * a + 1) := by
    intro a b h; simp only at h; omega
  have hcards : s.card = rothNumberNat ((m + 2) / 3) + rothNumberNat ((m + 1) / 3) := by
    rw [hs, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
      Finset.card_image_of_injective _ hinj2, hcardt, hcardu]
  have hlt : ∀ x ∈ s, x < m := by
    intro x hx
    rcases hmem x hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · have := Finset.mem_range.1 (hts hy); omega
    · have := Finset.mem_range.1 (hus hy); omega
  have hsf : ThreeAPFree (s : Set ℕ) := by
    intro a ha b hb c hc habc
    rcases hmem a ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;>
      rcases hmem b hb with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;>
        rcases hmem c hc with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩ <;>
          first
            | omega
            | (have := htf hx hy hz (by omega); omega)
            | (have := huf hx hy hz (by omega); omega)
  exact ThreeAPFree.le_rothNumberNat s hsf hlt hcards

/-- Iterating the split step down to the base values `r₃(m) ≥ m` for `m ≤ 2` (V001) and
`r₃(m) ≥ 5` for `m ≥ 9` (V003). -/
theorem szAux_le : ∀ fuel m, m ≤ fuel → szAux fuel m ≤ rothNumberNat m
  | 0, m, _ => by simp [szAux]
  | fuel + 1, m, h => by
      rw [szAux]
      split
      · have h1 := V001.min_two_le_rothNumberNat m
        omega
      · rename_i hm2
        split
        · exact V003.five_le_rothNumberNat (by omega)
        · rename_i hm9
          have hf1 : (m + 2) / 3 ≤ fuel := by omega
          have hf2 : (m + 1) / 3 ≤ fuel := by omega
          have ih1 := szAux_le fuel ((m + 2) / 3) hf1
          have ih2 := szAux_le fuel ((m + 1) / 3) hf2
          have hsplit := roth_split m
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
  maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V003.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V003.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V003.record record :=
  maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 249) (by decide) (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V004
