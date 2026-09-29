import SqueezeBench.Problems.Golomb.Records.Lower.V000.Def

/-!
# Golomb lower-bound record V000 — validity

The `C(m, 2)` two-element subsets of a ruler have distinct gaps, and every gap is a
positive integer at most `L`. The gap is written `2 * T.sup id - T.sum id` so that it is a
total function of `T`; on a pair `{a, b}` with `a < b` it is `b - a`.

Distinctness is exactly the Sidon property: `b - a = d - c` rearranges to `b + c = a + d`,
and `IsSidon` then forces the pairs to coincide.
-/

namespace SqueezeBench.Golomb.Lower.V000

open SqueezeBench Finset

/-- The gap of a two-element set, written to be total in `T`. -/
def spread (T : Finset ℕ) : ℕ := 2 * T.sup id - T.sum id

theorem spread_pair {a b : ℕ} (h : a < b) : spread {a, b} = b - a := by
  have hne : a ∉ ({b} : Finset ℕ) := by simp only [mem_singleton]; omega
  rw [spread, sum_insert hne, sum_singleton, sup_insert, sup_singleton]
  simp only [id_eq]
  rw [sup_eq_right.mpr (le_of_lt h)]
  omega

/-- A two-element finset of naturals, presented in increasing order. -/
theorem exists_pair {T : Finset ℕ} (h : T.card = 2) : ∃ a b, a < b ∧ T = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp h
  rcases Nat.lt_or_ge x y with h' | h'
  · exact ⟨x, y, h', rfl⟩
  · exact ⟨y, x, by omega, pair_comm x y⟩

theorem le_of_mem_rulerLengths {m L : ℕ} (hL : L ∈ RulerLengths m) : m * (m - 1) / 2 ≤ L := by
  obtain ⟨S, hsub, hcard, hsidon, _⟩ := hL
  have hbound : ∀ x ∈ S, x ≤ L := by
    intro x hx
    have := hsub hx
    rw [mem_range] at this
    omega
  have hmaps : ∀ T ∈ S.powersetCard 2, spread T ∈ Finset.Icc 1 L := by
    intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨a, b, hab, rfl⟩ := exists_pair hT.2
    have hb : b ≤ L := hbound b (hT.1 (by simp))
    rw [spread_pair hab, mem_Icc]
    omega
  have hinj : Set.InjOn spread (S.powersetCard 2) := by
    intro T hT T' hT' heq
    rw [mem_coe, mem_powersetCard] at hT hT'
    obtain ⟨a, b, hab, rfl⟩ := exists_pair hT.2
    obtain ⟨c, d, hcd, rfl⟩ := exists_pair hT'.2
    have ha : a ∈ S := hT.1 (by simp)
    have hb : b ∈ S := hT.1 (by simp)
    have hc : c ∈ S := hT'.1 (by simp)
    have hd : d ∈ S := hT'.1 (by simp)
    rw [spread_pair hab, spread_pair hcd] at heq
    have hsum : b + c = a + d := by omega
    rcases hsidon b hb c hc a ha d hd hsum with ⟨h1, _⟩ | ⟨h1, h2⟩
    · omega
    · rw [h1, h2]
  have hle := Finset.card_le_card_of_injOn spread hmaps hinj
  rw [card_powersetCard, hcard, Nat.choose_two_right, Nat.card_Icc] at hle
  omega

theorem valid : LowerBoundHolds f record := by
  intro m
  rcases Nat.lt_or_ge m nMin with h | h
  · have : m = 0 := by simpa [nMin] using h
    simp [record, this]
  · exact le_f h fun L hL => le_of_mem_rulerLengths hL

end SqueezeBench.Golomb.Lower.V000
