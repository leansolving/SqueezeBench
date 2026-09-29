import SqueezeBench.Problems.Schur.Records.Lower.V000.Def
import SqueezeBench.Problems.Schur.Finite

/-!
# Schur lower-bound record V000 — validity
-/

namespace SqueezeBench.Schur.Lower.V000

open SqueezeBench Finset

def schurRange (k : ℕ) : ℕ := (3 ^ k - 1) / 2

theorem schurRange_succ (k : ℕ) : schurRange (k + 1) = 3 * schurRange k + 1 := by
  obtain ⟨t, ht⟩ : ∃ t, 3 ^ k = 2 * t + 1 := by
    obtain ⟨s, hs⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
    exact ⟨s, by omega⟩
  simp only [schurRange, pow_succ, ht]
  omega

theorem one_le_schurRange {k : ℕ} (hk : 1 ≤ k) : 1 ≤ schurRange k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [schurRange_succ]
  omega

def schurColour : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n =>
      if n ≤ schurRange k then schurColour k n
      else if n ≤ 2 * schurRange k + 1 then k
      else schurColour k (n - (2 * schurRange k + 1))

theorem schurColour_lt : ∀ (k n : ℕ), schurColour (k + 1) n < k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n
    rw [schurColour]
    split
    · simp [schurColour]
    · split
      · omega
      · simp [schurColour]
  | succ k ih =>
    intro n
    rw [schurColour]
    split
    · exact Nat.lt_succ_of_lt (ih n)
    · split
      · omega
      · exact Nat.lt_succ_of_lt (ih _)

theorem schurColour_lt' {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : schurColour k n < k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact schurColour_lt j n

theorem schurColour_sumFree : ∀ (k x y : ℕ), 1 ≤ x → 1 ≤ y → x + y ≤ schurRange k →
    ¬ (schurColour k x = schurColour k y ∧ schurColour k y = schurColour k (x + y)) := by
  intro k
  induction k with
  | zero =>
    intro x y hx hy hsum _
    simp only [schurRange] at hsum
    omega
  | succ k ih =>
    intro x y hx hy hsum hcol
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp only [schurRange] at hsum
      omega
    have hM : 1 ≤ schurRange k := one_le_schurRange hk1
    set M := schurRange k with hMdef
    have hzr : x + y ≤ 3 * M + 1 := by rwa [schurRange_succ, ← hMdef] at hsum
    have hlt : ∀ n, schurColour k n < k := schurColour_lt' hk1
    have hlow : ∀ n, n ≤ M → schurColour (k + 1) n = schurColour k n := by
      intro n h; rw [schurColour, if_pos h]
    have hmid : ∀ n, M < n → n ≤ 2 * M + 1 → schurColour (k + 1) n = k := by
      intro n h1 h2; rw [schurColour, if_neg (by omega), if_pos h2]
    have hhigh : ∀ n, 2 * M + 1 < n →
        schurColour (k + 1) n = schurColour k (n - (2 * M + 1)) := by
      intro n h; rw [schurColour, if_neg (by omega), if_neg (by omega)]
    obtain ⟨hxy, hyz⟩ := hcol
    -- no argument may sit in the fresh middle block unless all do
    have hnotmid : ∀ n, schurColour (k + 1) n ≠ k → ¬ (M < n ∧ n ≤ 2 * M + 1) := by
      intro n hn ⟨h1, h2⟩
      exact hn (hmid n h1 h2)
    rcases Nat.lt_or_ge (2 * M + 1) (x + y) with hzhigh | hzlow
    · -- the sum is in the translated block
      have hzc : schurColour (k + 1) (x + y) < k := by
        rw [hhigh _ hzhigh]; exact hlt _
      have hxc : ¬ (M < x ∧ x ≤ 2 * M + 1) := hnotmid x (by omega)
      have hyc : ¬ (M < y ∧ y ≤ 2 * M + 1) := hnotmid y (by omega)
      rcases Nat.lt_or_ge (2 * M + 1) x with hxh | hxl
      · rcases Nat.lt_or_ge (2 * M + 1) y with hyh | hyl
        · omega
        · have hyle : y ≤ M := by omega
          have h1 : schurColour k (x - (2 * M + 1)) = schurColour k y := by
            rw [← hhigh x hxh, ← hlow y hyle]; exact hxy
          have h2 : schurColour k y = schurColour k ((x - (2 * M + 1)) + y) := by
            rw [← hlow y hyle, hyz, hhigh _ hzhigh]
            congr 1
            omega
          exact ih (x - (2 * M + 1)) y (by omega) (by omega) (by omega) ⟨h1, h2⟩
      · have hxle : x ≤ M := by omega
        have hyh : 2 * M + 1 < y := by omega
        have h1 : schurColour k x = schurColour k (y - (2 * M + 1)) := by
          rw [← hlow x hxle, ← hhigh y hyh]; exact hxy
        have h2 : schurColour k (y - (2 * M + 1)) = schurColour k (x + (y - (2 * M + 1))) := by
          rw [← hhigh y hyh, hyz, hhigh _ hzhigh]
          congr 1
          omega
        exact ih x (y - (2 * M + 1)) (by omega) (by omega) (by omega) ⟨h1, h2⟩
    · rcases Nat.lt_or_ge M (x + y) with hzmid | hzle
      · -- the sum is in the fresh block, so all three would have to be
        have hzc : schurColour (k + 1) (x + y) = k := hmid _ hzmid hzlow
        have hxc : schurColour (k + 1) x = k := by omega
        have hyc : schurColour (k + 1) y = k := by omega
        have hxm : M < x ∧ x ≤ 2 * M + 1 := by
          by_contra hc
          rcases Nat.lt_or_ge M x with h | h
          · exact hc ⟨h, by omega⟩
          · rw [hlow x (by omega)] at hxc
            exact absurd hxc (Nat.ne_of_lt (hlt x))
        have hym : M < y ∧ y ≤ 2 * M + 1 := by
          by_contra hc
          rcases Nat.lt_or_ge M y with h | h
          · exact hc ⟨h, by omega⟩
          · rw [hlow y (by omega)] at hyc
            exact absurd hyc (Nat.ne_of_lt (hlt y))
        omega
      · -- everything is in the low block
        have hxle : x ≤ M := by omega
        have hyle : y ≤ M := by omega
        have h1 : schurColour k x = schurColour k y := by
          rw [← hlow x hxle, ← hlow y hyle]; exact hxy
        have h2 : schurColour k y = schurColour k (x + y) := by
          rw [← hlow y hyle, ← hlow _ hzle]; exact hyz
        exact ih x y hx hy hzle ⟨h1, h2⟩

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (hN : Forces k N) : schurRange k + 1 ≤ N := by
  have hk1 : 1 ≤ k := by simpa [nMin] using hk
  by_contra hcon
  rw [Nat.not_le] at hcon
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxy, hyz⟩ :=
    hN (fun n => ⟨schurColour k n, schurColour_lt' hk1 n⟩)
  rw [mem_Icc] at hx hy hz
  have hxy' : schurColour k x = schurColour k y := by
    simpa using congrArg Fin.val hxy
  have hyz' : schurColour k y = schurColour k z := by
    simpa using congrArg Fin.val hyz
  refine schurColour_sumFree k x y hx.1 hy.1 (by omega) ⟨hxy', ?_⟩
  rw [hsum]
  exact hyz'

theorem valid : LowerBoundHolds f record := by
  intro k
  rcases Nat.lt_or_ge k nMin with h | h
  · have hk0 : k = 0 := by simpa [nMin] using h
    simp [record, hk0, f, nMin]
  · exact le_f h fun N hN => le_of_forces h hN

end SqueezeBench.Schur.Lower.V000
