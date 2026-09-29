import SqueezeBench.Problems.Golomb.Records.Upper.V000.Def

/-!
# Golomb upper-bound record V000 — validity

`Def.lean` for the problem already proves `f m ≤ 2^(m-1) - 1` via `binRuler`, so only the
quadratic ruler needs work here.

The multiplier is `2m²`, not `m²`: `IsSidon` here is stated on **sums**, so the residue to
separate is `i² + j² ≤ 2(m-1)²`, and `m²` would not dominate it. Given `aᵢ + aⱼ = a_k + a_l`,
uniqueness of division gives `i + j = k + l` and `i² + j² = k² + l²`, hence `ij = kl`, and
then `(i - k)(i - l) = 0` over `ℤ`.
-/

namespace SqueezeBench.Golomb.Upper.V000

open SqueezeBench Finset

/-- Uniqueness of division with remainder, in the form the Sidon check needs. -/
theorem div_unique {M q₁ r₁ q₂ r₂ : ℕ} (h₁ : r₁ < M) (h₂ : r₂ < M)
    (h : M * q₁ + r₁ = M * q₂ + r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  have hq : q₁ = q₂ := by
    rcases lt_trichotomy q₁ q₂ with hlt | heq | hgt
    · exfalso
      have : M * q₁ + M ≤ M * q₂ := by
        calc M * q₁ + M = M * (q₁ + 1) := by ring
          _ ≤ M * q₂ := Nat.mul_le_mul_left M hlt
      omega
    · exact heq
    · exfalso
      have : M * q₂ + M ≤ M * q₁ := by
        calc M * q₂ + M = M * (q₂ + 1) := by ring
          _ ≤ M * q₁ := Nat.mul_le_mul_left M hgt
      omega
  refine ⟨hq, ?_⟩
  rw [hq] at h
  omega

/-- The quadratic ruler `aᵢ = 2m²·i + i²` for `i < m`. -/
def quadRuler (m : ℕ) : Finset ℕ := (range m).image (fun i => 2 * m ^ 2 * i + i ^ 2)


theorem quadRuler_strictMono {m i j : ℕ} (h : i < j) :
    2 * m ^ 2 * i + i ^ 2 < 2 * m ^ 2 * j + j ^ 2 := by
  have h1 : 2 * m ^ 2 * i ≤ 2 * m ^ 2 * j := Nat.mul_le_mul_left _ (le_of_lt h)
  have h2 : i ^ 2 < j ^ 2 := Nat.pow_lt_pow_left h (by omega)
  omega

theorem quadRuler_card (m : ℕ) : (quadRuler m).card = m := by
  rw [quadRuler, card_image_of_injective _ ?_, card_range]
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (Nat.ne_of_lt (quadRuler_strictMono h))
  · exact h
  · exact absurd hij.symm (Nat.ne_of_lt (quadRuler_strictMono h))

theorem quadRuler_sidon (m : ℕ) : IsSidon (quadRuler m) := by
  have hres : ∀ i ∈ range m, ∀ j ∈ range m, i ^ 2 + j ^ 2 < 2 * m ^ 2 := by
    intro i hi j hj
    rw [mem_range] at hi hj
    have h1 : i ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hi (by omega)
    have h2 : j ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hj (by omega)
    omega
  intro a ha b hb c hc d hd habcd
  simp only [quadRuler, mem_image] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨l, hl, rfl⟩ := hd
  have hgroup : 2 * m ^ 2 * (i + j) + (i ^ 2 + j ^ 2)
      = 2 * m ^ 2 * (k + l) + (k ^ 2 + l ^ 2) := by ring_nf; ring_nf at habcd; omega
  obtain ⟨hsum, hsq⟩ := div_unique (hres i hi j hj) (hres k hk l hl) hgroup
  have hprod : i * j = k * l := by nlinarith [hsum, hsq]
  have hz : ((i : ℤ) - k) * ((i : ℤ) - l) = 0 := by
    have e1 : (i : ℤ) + j = (k : ℤ) + l := by exact_mod_cast hsum
    have e2 : (i : ℤ) * j = (k : ℤ) * l := by exact_mod_cast hprod
    linear_combination (i : ℤ) * e1 - e2
  rcases mul_eq_zero.mp hz with h | h
  · have hik : i = k := by exact_mod_cast sub_eq_zero.mp h
    left
    exact ⟨by rw [hik], by rw [show j = l by omega]⟩
  · have hil : i = l := by exact_mod_cast sub_eq_zero.mp h
    right
    exact ⟨by rw [hil], by rw [show j = k by omega]⟩

theorem quadLen_mem (m : ℕ) (hm : nMin ≤ m) : quadLen m ∈ RulerLengths m := by
  have hm1 : 1 ≤ m := by simpa [nMin] using hm
  refine ⟨quadRuler m, ?_, quadRuler_card m, quadRuler_sidon m, ?_⟩
  · intro x hx
    simp only [quadRuler, mem_image, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_range, quadLen]
    have h1 : 2 * m ^ 2 * i ≤ 2 * m ^ 2 * (m - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : i ^ 2 ≤ (m - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  · simp only [quadRuler, mem_image, mem_range, quadLen]
    exact ⟨m - 1, by omega, rfl⟩


theorem base_valid : UpperBoundHolds f base := by
  refine minWith_valid ?_ ?_ <;> intro m <;>
    rcases Nat.lt_or_ge m nMin with h | h
  · have : m = 0 := by simpa [nMin] using h
    simp [f, this, nMin]
  · exact f_le_binRuler m h
  · have : m = 0 := by simpa [nMin] using h
    simp [f, this, nMin, quadLen]
  · exact f_le_of_mem h (quadLen_mem m h)

/-- `{0, 1, 4, 9, 11}` witnesses that `11` is an attainable 5-mark ruler length. -/
theorem eleven_mem : (11 : ℕ) ∈ RulerLengths 5 :=
  ⟨{0, 1, 4, 9, 11}, by decide, by decide, by decide, by decide⟩

/-- `{0, 1, 4, 10, 12, 17}` witnesses that `17` is an attainable 6-mark ruler length. -/
theorem seventeen_mem : (17 : ℕ) ∈ RulerLengths 6 :=
  ⟨{0, 1, 4, 10, 12, 17}, by decide, by decide, by decide, by decide⟩

theorem valid : UpperBoundHolds f record :=
  patch_valid' (patch_valid' base_valid (f_le_of_mem (by decide) eleven_mem))
    (f_le_of_mem (by decide) seventeen_mem)

end SqueezeBench.Golomb.Upper.V000
