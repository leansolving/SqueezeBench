import SqueezeBench.Problems.Schur.Records.Lower.V001.Def
import SqueezeBench.Problems.Schur.Records.Lower.V000.Proof

/-! Record V001 for Schur, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Schur/Lower/V001.lean`.

The seed V000 hard-wires the tripling construction into one recursive colouring starting from
the empty one. Here the construction is split in two: `SumFreeCol` names the property "this
`k`-colouring of `[1, M]` has no monochromatic `x + y = z`", `ext_sumFree` is the tripling step
`SumFreeCol k M c → SumFreeCol (k+1) (3M+1) (ext c M k)`, and the tower may then be started
anywhere. It is started at the explicit optimal 4-colouring `col4` of `[1, 44]`, so
`S(4+j) ≥ (89·3^j − 1)/2`.
-/

namespace SqueezeBench.Schur.Lower.V001

open SqueezeBench Finset

-- A `k`-colouring of `ℕ` whose restriction to `[1, M]` has no monochromatic `x + y = z`.
def SumFreeCol (k M : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ n, c n < k) ∧
    ∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ M → ¬ (c x = c y ∧ c y = c (x + y))

theorem le_f_of_col {k M : ℕ} {c : ℕ → ℕ} (hk : nMin ≤ k) (h : SumFreeCol k M c) : M ≤ f k := by
  refine le_f hk fun N hN => ?_
  by_contra hcon
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxy, hyz⟩ := hN (fun n => ⟨c n, h.1 n⟩)
  rw [mem_Icc] at hx hy hz
  have hxy' : c x = c y := by simpa using congrArg Fin.val hxy
  have hyz' : c y = c z := by simpa using congrArg Fin.val hyz
  exact h.2 x y hx.1 hy.1 (by omega) ⟨hxy', by rw [hsum]; exact hyz'⟩

-- The tripling step: `[1, M]` keeps its colours, `[M+1, 2M+1]` gets the fresh colour `k`, and
-- `[2M+2, 3M+1]` repeats `[1, M]` translated by `2M+1`.
def ext (c : ℕ → ℕ) (M k : ℕ) : ℕ → ℕ := fun n =>
  if n ≤ M then c n else if n ≤ 2 * M + 1 then k else c (n - (2 * M + 1))

theorem ext_sumFree {k M : ℕ} {c : ℕ → ℕ} (h : SumFreeCol k M c) :
    SumFreeCol (k + 1) (3 * M + 1) (ext c M k) := by
  obtain ⟨hlt, hsf⟩ := h
  have hlow : ∀ n, n ≤ M → ext c M k n = c n := by
    intro n hn; simp only [ext, if_pos hn]
  have hmid : ∀ n, M < n → n ≤ 2 * M + 1 → ext c M k n = k := by
    intro n h1 h2; simp only [ext, if_neg (by omega : ¬ n ≤ M), if_pos h2]
  have hhigh : ∀ n, 2 * M + 1 < n → ext c M k n = c (n - (2 * M + 1)) := by
    intro n hn
    simp only [ext, if_neg (by omega : ¬ n ≤ M), if_neg (by omega : ¬ n ≤ 2 * M + 1)]
  refine ⟨fun n => ?_, ?_⟩
  · rcases Nat.lt_or_ge M n with h | h
    · rcases Nat.lt_or_ge (2 * M + 1) n with h' | h'
      · exact Nat.lt_succ_of_lt (by rw [hhigh n h']; exact hlt _)
      · rw [hmid n h h']; omega
    · exact Nat.lt_succ_of_lt (by rw [hlow n h]; exact hlt n)
  intro x y hx hy hsum ⟨hxy, hyz⟩
  -- no argument carries the fresh colour `k` unless all three do
  have hnotmid : ∀ n, ext c M k n ≠ k → ¬ (M < n ∧ n ≤ 2 * M + 1) := by
    intro n hn ⟨h1, h2⟩; exact hn (hmid n h1 h2)
  rcases Nat.lt_or_ge (2 * M + 1) (x + y) with hzhigh | hzlow
  · -- the sum lies in the translated block, so no argument is in the fresh block
    have hzc : ext c M k (x + y) < k := by rw [hhigh _ hzhigh]; exact hlt _
    have hxc : ¬ (M < x ∧ x ≤ 2 * M + 1) := hnotmid x (by omega)
    have hyc : ¬ (M < y ∧ y ≤ 2 * M + 1) := hnotmid y (by omega)
    rcases Nat.lt_or_ge (2 * M + 1) x with hxh | hxl
    · have hyle : y ≤ M := by omega
      refine hsf (x - (2 * M + 1)) y (by omega) hy (by omega) ⟨?_, ?_⟩
      · rw [← hhigh x hxh, ← hlow y hyle]; exact hxy
      · rw [← hlow y hyle, hyz, hhigh _ hzhigh]; congr 1; omega
    · have hxle : x ≤ M := by omega
      have hyh : 2 * M + 1 < y := by omega
      refine hsf x (y - (2 * M + 1)) hx (by omega) (by omega) ⟨?_, ?_⟩
      · rw [← hlow x hxle, ← hhigh y hyh]; exact hxy
      · rw [← hhigh y hyh, hyz, hhigh _ hzhigh]; congr 1; omega
  · rcases Nat.lt_or_ge M (x + y) with hzmid | hzle
    · -- the sum lies in the fresh block, so both arguments would have to as well
      have hzc : ext c M k (x + y) = k := hmid _ hzmid hzlow
      have hxm : M < x ∧ x ≤ 2 * M + 1 := by
        by_contra hcon
        rcases Nat.lt_or_ge M x with h | h
        · exact hcon ⟨h, by omega⟩
        · have := hlt x; rw [hlow x h] at hxy; omega
      have hym : M < y ∧ y ≤ 2 * M + 1 := by
        by_contra hcon
        rcases Nat.lt_or_ge M y with h | h
        · exact hcon ⟨h, by omega⟩
        · have := hlt y; rw [hlow y h] at hyz; omega
      omega
    · -- everything lies in the low block
      refine hsf x y hx hy hzle ⟨?_, ?_⟩
      · rw [← hlow x (by omega), ← hlow y (by omega)]; exact hxy
      · rw [← hlow y (by omega), ← hlow _ hzle]; exact hyz

-- The range reached after `j` tripling steps from `[1, M]`.
def G (M j : ℕ) : ℕ := ((2 * M + 1) * 3 ^ j - 1) / 2

theorem G_zero (M : ℕ) : G M 0 = M := by simp [G]

theorem G_succ (M j : ℕ) : G M (j + 1) = 3 * G M j + 1 := by
  obtain ⟨t, ht⟩ : ∃ t, (2 * M + 1) * 3 ^ j = 2 * t + 1 := by
    obtain ⟨s, hs⟩ := (Odd.mul (⟨M, by omega⟩ : Odd (2 * M + 1))
      (Odd.pow (by decide : Odd 3)) : Odd ((2 * M + 1) * 3 ^ j))
    exact ⟨s, by omega⟩
  simp only [G, pow_succ, ← Nat.mul_assoc, ht]
  omega

theorem exists_col_grow {k M : ℕ} {c : ℕ → ℕ} (h : SumFreeCol k M c) (j : ℕ) :
    ∃ d, SumFreeCol (k + j) (G M j) d := by
  induction j with
  | zero => exact ⟨c, by rw [G_zero]; exact h⟩
  | succ j ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨ext d (G M j) (k + j), by rw [G_succ, ← Nat.add_assoc]; exact ext_sumFree hd⟩

-- An explicit optimal sum-free 4-colouring of `[1, 44]`, packed base 4 into one numeral:
-- colour `n` is digit `n`. Digits above 44 are `0`, which is harmless.
def col4 (n : ℕ) : ℕ := 87760291276531217347731984 / 4 ^ n % 4

theorem col4_check : ∀ x < 45, ∀ y < 45, (1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ 44) →
    ¬ (col4 x = col4 y ∧ col4 y = col4 (x + y)) := by decide +kernel

theorem col4_sumFree : SumFreeCol 4 44 col4 := by
  refine ⟨fun n => Nat.mod_lt _ (by omega), fun x y hx hy hxy => ?_⟩
  exact col4_check x (by omega) y (by omega) ⟨hx, hy, hxy⟩

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f v := by
  refine SqueezeBench.pin_lowerBoundHolds fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = 4 + j := ⟨k - 4, by omega⟩
  obtain ⟨d, hd⟩ := exists_col_grow col4_sumFree j
  have := le_f_of_col (k := 4 + j) (by rw [nMin_eq]; omega) hd
  simpa [G] using this

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Schur.Lower.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V000.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V000.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Schur.nMin) (n₀ := 4) (by decide) (by decide)

end SqueezeBench.Schur.Lower.V001
