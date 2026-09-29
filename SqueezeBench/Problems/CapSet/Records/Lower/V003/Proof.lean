import SqueezeBench.Problems.CapSet.Records.Lower.V003.Def
import SqueezeBench.Problems.CapSet.Records.Lower.V002.Proof

/-! Record V003 for CapSet, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Lower/V003.lean`. -/

namespace SqueezeBench.CapSet.Lower.V003

open SqueezeBench SqueezeBench.CapSet Finset

-- ## Base-3 codes. A point of `F₃ⁿ` is the number `∑ vᵢ 3ⁱ < 3ⁿ`; `dg i c` is its digit `i`.

def dg (i c : ℕ) : ℕ := c / 3 ^ i % 3

theorem dg_lt (i c : ℕ) : dg i c < 3 := Nat.mod_lt _ (by norm_num)

theorem dg_succ (i c : ℕ) : dg (i + 1) c = dg i (c / 3) := by
  unfold dg
  rw [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]

-- Adding a multiple of `3 ^ (i + 1)` leaves digit `i` unchanged.
theorem dg_add_mul (i c m : ℕ) : dg i (c + m * 3 ^ (i + 1)) = dg i c := by
  unfold dg
  rw [pow_succ, mul_comm (3 ^ i) 3, ← mul_assoc, Nat.add_mul_div_right _ _ (by positivity),
    Nat.add_mul_mod_self_right]

-- Digit `i` of `T + m * 3 ^ i` is `m % 3` when `T < 3 ^ i`.
theorem dg_add_of_lt {i T : ℕ} (hT : T < 3 ^ i) (m : ℕ) : dg i (T + m * 3 ^ i) = m % 3 := by
  unfold dg
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hT, zero_add]

-- Digits below `i` of `T + m * 3 ^ i` are those of `T`.
theorem dg_add_of_lt' {i j : ℕ} (hj : j < i) (T m : ℕ) : dg j (T + m * 3 ^ i) = dg j T := by
  obtain ⟨k, rfl⟩ : ∃ k, i = j + 1 + k := ⟨i - (j + 1), by omega⟩
  rw [pow_add, show m * (3 ^ (j + 1) * 3 ^ k) = m * 3 ^ k * 3 ^ (j + 1) by ring, dg_add_mul]

-- Two codes below `3 ^ n` with the same `n` digits are equal.
theorem eq_of_dg_eq : ∀ (n c c' : ℕ), c < 3 ^ n → c' < 3 ^ n →
    (∀ i < n, dg i c = dg i c') → c = c'
  | 0, c, c', hc, hc', _ => by simp at hc hc'; omega
  | n + 1, c, c', hc, hc', h => by
    have h0 := h 0 (by omega)
    simp only [dg, pow_zero, Nat.div_one] at h0
    rw [pow_succ] at hc hc'
    have hrec := eq_of_dg_eq n (c / 3) (c' / 3) (by omega) (by omega)
      (fun i hi => by have := h (i + 1) (by omega); rwa [dg_succ, dg_succ] at this)
    omega

-- `T + m * B < K * B ↔ m < K` when `T < B`.
theorem add_mul_lt_iff {T m B K : ℕ} (hT : T < B) : T + m * B < K * B ↔ m < K := by
  have hB : 0 < B := by omega
  rw [← Nat.div_lt_iff_lt_mul hB, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hT, zero_add]

-- ## Slice masks. Bit `c` of `S n i` is set exactly when `c < 3 ^ n` and digit `i` of `c` is `0`.

def S (n i : ℕ) : ℕ := (2 ^ 3 ^ i - 1) * ((2 ^ 3 ^ n - 1) / (2 ^ 3 ^ (i + 1) - 1))

-- `pat` repeated `k` times with period `P`.
def rep (pat P : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ P * rep pat P k + pat

theorem rep_eq_sum (pat P k : ℕ) : rep pat P k = ∑ j ∈ range k, pat * (2 ^ P) ^ j := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [sum_range_succ', rep, ih, mul_sum, pow_zero, mul_one]
    congr 1
    exact sum_congr rfl fun j _ => by ring

theorem testBit_rep {pat P : ℕ} (hpat : pat < 2 ^ P) (hP : 0 < P) (k c : ℕ) :
    (rep pat P k).testBit c = (decide (c / P < k) && pat.testBit (c % P)) := by
  induction k generalizing c with
  | zero => simp [rep]
  | succ k ih =>
    rw [rep, Nat.testBit_two_pow_mul_add _ hpat]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp
    · simp only [not_lt] at h
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + P := ⟨c - P, by omega⟩
      rw [Nat.add_sub_cancel, ih, Nat.add_div_right _ hP, Nat.add_mod_right]
      simp

theorem S_eq_rep {n i : ℕ} (hi : i < n) :
    S n i = rep (2 ^ 3 ^ i - 1) (3 ^ (i + 1)) (3 ^ (n - 1 - i)) := by
  have h2 : 2 ≤ 2 ^ 3 ^ (i + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 3 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by norm_num))
  have hpow : (2 ^ 3 ^ (i + 1)) ^ 3 ^ (n - 1 - i) = 2 ^ 3 ^ n := by
    rw [← pow_mul, ← pow_add, show i + 1 + (n - 1 - i) = n by omega]
  rw [rep_eq_sum, ← mul_sum, Nat.geomSum_eq h2, hpow]
  rfl

theorem testBit_S {n i : ℕ} (hi : i < n) (c : ℕ) :
    (S n i).testBit c = decide (c < 3 ^ n ∧ dg i c = 0) := by
  have hpat : 2 ^ 3 ^ i - 1 < 2 ^ 3 ^ (i + 1) :=
    lt_of_lt_of_le (Nat.sub_lt (by positivity) (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [S_eq_rep hi, testBit_rep hpat (by positivity), Nat.testBit_two_pow_sub_one]
  have h1 : c / 3 ^ (i + 1) < 3 ^ (n - 1 - i) ↔ c < 3 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show n - 1 - i + (i + 1) = n by omega]
  have h2 : c % 3 ^ (i + 1) < 3 ^ i ↔ dg i c = 0 := by
    unfold dg
    rw [pow_succ, ← Nat.mod_mul_right_div_self, Nat.div_eq_zero_iff]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · exact absurd h (by positivity)
      · exact h
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [h1, h2]

-- The mask of the codes below `3 ^ n` whose digit `i` is `u`, read at `T + m * 3 ^ i`.
theorem testBit_S_shift {n i u T : ℕ} (hi : i < n) (hu : u < 3) (hT : T < 3 ^ i) (m : ℕ) :
    (S n i <<< (u * 3 ^ i)).testBit (T + m * 3 ^ i) =
      decide (m < 3 * 3 ^ (n - 1 - i) ∧ m % 3 = u) := by
  have h3n : 3 ^ n = 3 * 3 ^ (n - 1 - i) * 3 ^ i := by
    rw [mul_assoc, ← pow_add, ← pow_succ', show n - 1 - i + i + 1 = n by omega]
  rw [Nat.testBit_shiftLeft]
  by_cases hmu : u ≤ m
  · have hle : u * 3 ^ i ≤ T + m * 3 ^ i := le_add_left (Nat.mul_le_mul_right _ hmu)
    rw [decide_eq_true (show T + m * 3 ^ i ≥ u * 3 ^ i from hle), Bool.true_and,
      Nat.add_sub_assoc (Nat.mul_le_mul_right _ hmu), ← Nat.sub_mul, testBit_S hi,
      dg_add_of_lt hT, decide_eq_decide, h3n, add_mul_lt_iff hT]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  · have hmu := not_le.mp hmu
    have hlt : T + m * 3 ^ i < u * 3 ^ i :=
      calc T + m * 3 ^ i < 3 ^ i + m * 3 ^ i := Nat.add_lt_add_right hT _
        _ = (m + 1) * 3 ^ i := by ring
        _ ≤ u * 3 ^ i := Nat.mul_le_mul_right _ hmu
    rw [decide_eq_false (not_le.mpr hlt), Bool.false_and, eq_comm, decide_eq_false_iff_not]
    omega

-- ## Transposing two slices of a mask, and the reflection `y ↦ -(x + y)` as six of them.

-- The transposition of the digit values `a` and `b`.
def tr (a b v : ℕ) : ℕ := if v = a then b else if v = b then a else v

-- Transposes the slices `a < b` along axis `i` of a mask of codes below `3 ^ n`.
def swp (n i a b M : ℕ) : ℕ :=
  (M &&& (S n i <<< ((3 - a - b) * 3 ^ i)))
  ||| ((M &&& (S n i <<< (a * 3 ^ i))) <<< ((b - a) * 3 ^ i))
  ||| ((M &&& (S n i <<< (b * 3 ^ i))) >>> ((b - a) * 3 ^ i))

theorem testBit_term0 {n i u T : ℕ} (hi : i < n) (hu : u < 3) (hT : T < 3 ^ i) (m M : ℕ) :
    (M &&& (S n i <<< (u * 3 ^ i))).testBit (T + m * 3 ^ i) =
      (M.testBit (T + m * 3 ^ i) && decide (m < 3 * 3 ^ (n - 1 - i) ∧ m % 3 = u)) := by
  rw [Nat.testBit_and, testBit_S_shift hi hu hT]

theorem testBit_term1 {n i a e T : ℕ} (hi : i < n) (ha : a < 3) (hT : T < 3 ^ i) (m M : ℕ) :
    ((M &&& (S n i <<< (a * 3 ^ i))) <<< (e * 3 ^ i)).testBit (T + m * 3 ^ i) =
      if e ≤ m then
        (M.testBit (T + (m - e) * 3 ^ i) &&
          decide (m - e < 3 * 3 ^ (n - 1 - i) ∧ (m - e) % 3 = a))
      else false := by
  rw [Nat.testBit_shiftLeft]
  split_ifs with he
  · have hle : e * 3 ^ i ≤ T + m * 3 ^ i := le_add_left (Nat.mul_le_mul_right _ he)
    rw [decide_eq_true (show T + m * 3 ^ i ≥ e * 3 ^ i from hle), Bool.true_and,
      Nat.add_sub_assoc (Nat.mul_le_mul_right _ he), ← Nat.sub_mul, testBit_term0 hi ha hT]
  · have hlt : T + m * 3 ^ i < e * 3 ^ i :=
      calc T + m * 3 ^ i < 3 ^ i + m * 3 ^ i := Nat.add_lt_add_right hT _
        _ = (m + 1) * 3 ^ i := by ring
        _ ≤ e * 3 ^ i := Nat.mul_le_mul_right _ (by omega)
    rw [decide_eq_false (not_le.mpr hlt), Bool.false_and]

theorem testBit_term2 {n i b e T : ℕ} (hi : i < n) (hb : b < 3) (hT : T < 3 ^ i) (m M : ℕ) :
    ((M &&& (S n i <<< (b * 3 ^ i))) >>> (e * 3 ^ i)).testBit (T + m * 3 ^ i) =
      (M.testBit (T + (m + e) * 3 ^ i) &&
        decide (m + e < 3 * 3 ^ (n - 1 - i) ∧ (m + e) % 3 = b)) := by
  rw [Nat.testBit_shiftRight, show e * 3 ^ i + (T + m * 3 ^ i) = T + (m + e) * 3 ^ i by ring,
    testBit_term0 hi hb hT]

theorem testBit_swp {n i a b T m : ℕ} (hi : i < n) (hab : a < b) (hb : b < 3) (hT : T < 3 ^ i)
    (hm : m < 3 * 3 ^ (n - 1 - i)) (M : ℕ) :
    (swp n i a b M).testBit (T + m * 3 ^ i) =
      M.testBit (T + (m - m % 3 + tr a b (m % 3)) * 3 ^ i) := by
  unfold swp
  rw [Nat.testBit_or, Nat.testBit_or, testBit_term0 (u := 3 - a - b) hi (by omega) hT,
    testBit_term1 (a := a) (e := b - a) hi (by omega) hT, testBit_term2 (b := b) (e := b - a) hi hb hT]
  have hm3 := Nat.mod_lt m (show 3 > 0 by norm_num)
  rcases (by omega : m % 3 = 3 - a - b ∨ m % 3 = a ∨ m % 3 = b) with h | h | h
  · rw [show m - m % 3 + tr a b (m % 3) = m by unfold tr; split_ifs; all_goals omega,
      decide_eq_true (by omega : m < 3 * 3 ^ (n - 1 - i) ∧ m % 3 = 3 - a - b),
      decide_eq_false (by omega : ¬ (m + (b - a) < 3 * 3 ^ (n - 1 - i) ∧ (m + (b - a)) % 3 = b))]
    split_ifs with he
    · rw [decide_eq_false (by omega : ¬ (m - (b - a) < 3 * 3 ^ (n - 1 - i) ∧ (m - (b - a)) % 3 = a))]
      simp
    · simp
  · rw [show m - m % 3 + tr a b (m % 3) = m + (b - a) by unfold tr; split_ifs; all_goals omega,
      decide_eq_false (by omega : ¬ (m < 3 * 3 ^ (n - 1 - i) ∧ m % 3 = 3 - a - b)),
      decide_eq_true (by omega : m + (b - a) < 3 * 3 ^ (n - 1 - i) ∧ (m + (b - a)) % 3 = b)]
    split_ifs with he
    · rw [decide_eq_false (by omega : ¬ (m - (b - a) < 3 * 3 ^ (n - 1 - i) ∧ (m - (b - a)) % 3 = a))]
      simp
    · simp
  · rw [show m - m % 3 + tr a b (m % 3) = m - (b - a) by unfold tr; split_ifs; all_goals omega,
      decide_eq_false (by omega : ¬ (m < 3 * 3 ^ (n - 1 - i) ∧ m % 3 = 3 - a - b)),
      decide_eq_false (by omega : ¬ (m + (b - a) < 3 * 3 ^ (n - 1 - i) ∧ (m + (b - a)) % 3 = b)),
      if_pos (by omega : b - a ≤ m),
      decide_eq_true (by omega : m - (b - a) < 3 * 3 ^ (n - 1 - i) ∧ (m - (b - a)) % 3 = a)]
    simp

-- Along axis `i`, the reflection `v ↦ -(xᵢ + v)` of the digit values is a transposition.
def reflAx (n i x M : ℕ) : ℕ :=
  if dg i x = 0 then swp n i 1 2 M else if dg i x = 1 then swp n i 0 2 M else swp n i 0 1 M

theorem testBit_reflAx {n i x T m : ℕ} (hi : i < n) (hT : T < 3 ^ i)
    (hm : m < 3 * 3 ^ (n - 1 - i)) (M : ℕ) :
    (reflAx n i x M).testBit (T + m * 3 ^ i) =
      M.testBit (T + (m - m % 3 + (2 * (dg i x + m % 3)) % 3) * 3 ^ i) := by
  have hx := dg_lt i x
  have hm3 := Nat.mod_lt m (show 3 > 0 by norm_num)
  unfold reflAx
  rcases (by omega : dg i x = 0 ∨ dg i x = 1 ∨ dg i x = 2) with h | h | h
  · rw [if_pos h, testBit_swp hi (by norm_num) (by norm_num) hT hm, h]
    congr 3
    unfold tr; split_ifs <;> omega
  · rw [if_neg (by omega), if_pos h, testBit_swp hi (by norm_num) (by norm_num) hT hm, h]
    congr 3
    unfold tr; split_ifs <;> omega
  · rw [if_neg (by omega), if_neg (by omega), testBit_swp hi (by norm_num) (by norm_num) hT hm, h]
    congr 3
    unfold tr; split_ifs <;> omega

-- Reflecting the first `k` axes, and all `n` of them.
def reflUpTo (n x M : ℕ) : ℕ → ℕ
  | 0 => M
  | k + 1 => reflAx n k x (reflUpTo n x M k)

def refl (n x M : ℕ) : ℕ := reflUpTo n x M n

-- The code of `-(x + c)` on the first `k` digits: `-(u + v) = 2 * (u + v)` in `ZMod 3`.
def thd (x c : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => thd x c k + (2 * (dg k x + dg k c)) % 3 * 3 ^ k

theorem thd_lt (x c k : ℕ) : thd x c k < 3 ^ k := by
  induction k with
  | zero => simp [thd]
  | succ k ih =>
    rw [thd, pow_succ]
    have h2 : (2 * (dg k x + dg k c)) % 3 ≤ 2 := by omega
    have h := Nat.mul_le_mul_right (3 ^ k) h2
    omega

theorem dg_thd {x c k j : ℕ} (hj : j < k) : dg j (thd x c k) = (2 * (dg j x + dg j c)) % 3 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [thd]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · rw [dg_add_of_lt' h, ih h]
    · rw [dg_add_of_lt (thd_lt x c j), Nat.mod_mod]

theorem thd_congr {x c c' k : ℕ} (h : ∀ j < k, dg j c = dg j c') : thd x c k = thd x c' k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [thd, thd, ih (fun j hj => h j (by omega)), h k (by omega)]

theorem testBit_reflUpTo {n x c : ℕ} (hc : c < 3 ^ n) (M : ℕ) :
    ∀ k, k ≤ n → (reflUpTo n x M k).testBit c = M.testBit (thd x c k + c / 3 ^ k * 3 ^ k)
  | 0, _ => by simp [reflUpTo, thd]
  | k + 1, hk => by
    have hB : 0 < 3 ^ k := by positivity
    have hT : c % 3 ^ k < 3 ^ k := Nat.mod_lt _ hB
    have h3n : 3 ^ n = 3 * 3 ^ (n - 1 - k) * 3 ^ k := by
      rw [mul_assoc, ← pow_add, ← pow_succ', show n - 1 - k + k + 1 = n by omega]
    have hm : c / 3 ^ k < 3 * 3 ^ (n - 1 - k) := by
      rw [Nat.div_lt_iff_lt_mul hB, ← h3n]; exact hc
    have hm' : c / 3 ^ k - c / 3 ^ k % 3 + (2 * (dg k x + c / 3 ^ k % 3)) % 3
        < 3 * 3 ^ (n - 1 - k) := by
      have hq := (Nat.div_add_mod (c / 3 ^ k) 3).symm
      have hd : (2 * (dg k x + c / 3 ^ k % 3)) % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hq' : c / 3 ^ k / 3 < 3 ^ (n - 1 - k) := by omega
      omega
    have hc' : c % 3 ^ k + (c / 3 ^ k - c / 3 ^ k % 3 + (2 * (dg k x + c / 3 ^ k % 3)) % 3) * 3 ^ k
        < 3 ^ n := by
      rw [h3n, add_mul_lt_iff hT]; exact hm'
    have hsplit : c = c % 3 ^ k + c / 3 ^ k * 3 ^ k := by rw [mul_comm, Nat.mod_add_div]
    have hthd : thd x (c % 3 ^ k + (c / 3 ^ k - c / 3 ^ k % 3 +
        (2 * (dg k x + c / 3 ^ k % 3)) % 3) * 3 ^ k) k = thd x c k :=
      thd_congr fun j hj => by
        rw [dg_add_of_lt' hj]
        conv_rhs => rw [hsplit]
        rw [dg_add_of_lt' hj]
    rw [reflUpTo]
    conv_lhs => rw [hsplit]
    rw [testBit_reflAx (by omega) hT hm, testBit_reflUpTo hc' M k (by omega), hthd,
      Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hT, zero_add, thd, pow_succ,
      ← Nat.div_div_eq_div_mul]
    congr 1
    have h3 : c / 3 ^ k - c / 3 ^ k % 3 = 3 * (c / 3 ^ k / 3) := by omega
    rw [show dg k c = c / 3 ^ k % 3 from rfl, h3]
    ring

theorem testBit_refl {n x c : ℕ} (hc : c < 3 ^ n) (M : ℕ) :
    (refl n x M).testBit c = M.testBit (thd x c n) := by
  rw [refl, testBit_reflUpTo hc M n le_rfl, Nat.div_eq_of_lt hc, zero_mul, add_zero]

-- ## From codes to points of `F₃ⁿ`, and the cap criterion.

def dec (n c : ℕ) : Fin n → ZMod 3 := fun i => (dg i c : ZMod 3)

theorem dec_thd (n x c : ℕ) : dec n (thd x c n) = -(dec n x + dec n c) := by
  have h : ∀ a b : ZMod 3, (2 : ZMod 3) * (a + b) = -(a + b) := by decide
  funext i
  simp only [dec, Pi.neg_apply, Pi.add_apply]
  rw [dg_thd i.isLt, ZMod.natCast_mod]
  push_cast
  exact h _ _

theorem dec_inj {n c c' : ℕ} (hc : c < 3 ^ n) (hc' : c' < 3 ^ n) (h : dec n c = dec n c') :
    c = c' := by
  refine eq_of_dg_eq n c c' hc hc' fun i hi => ?_
  have this : ((dg i c : ℕ) : ZMod 3) = ((dg i c' : ℕ) : ZMod 3) := congrFun h ⟨i, hi⟩
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (dg_lt i c),
    Nat.mod_eq_of_lt (dg_lt i c')] at this

theorem thd_thd {n x c : ℕ} (hc : c < 3 ^ n) : thd x (thd x c n) n = c := by
  refine eq_of_dg_eq n _ _ (thd_lt _ _ _) hc fun i hi => ?_
  rw [dg_thd hi, dg_thd hi]
  have := dg_lt i x
  have := dg_lt i c
  omega

theorem thd_self {n x : ℕ} (hx : x < 3 ^ n) : thd x x n = x := by
  refine eq_of_dg_eq n _ _ (thd_lt _ _ _) hx fun i hi => ?_
  rw [dg_thd hi]
  have := dg_lt i x
  omega

-- A list of codes whose mask `M` is disjoint from each of its reflections (except at the
-- centre) decodes to a cap: the third point `-(x + y)` of two of its points is never one of them.
theorem threeAPFree_of_mask (n : ℕ) (codes : List ℕ) (M : ℕ)
    (hlt : ∀ c ∈ codes, c < 3 ^ n)
    (hmem : ∀ c ∈ codes, M.testBit c = true)
    (hpair : ∀ x ∈ codes, M &&& refl n x M = 1 <<< x) :
    ThreeAPFree ((codes.map (dec n)).toFinset : Set (Fin n → ZMod 3)) := by
  intro a ha b hb c hc habc
  rw [mem_coe, List.mem_toFinset, List.mem_map] at ha hb hc
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  obtain ⟨z, hz, rfl⟩ := hc
  have hsolve : ∀ u v w : ZMod 3, u + w = v + v → w = -(u + v) := by decide
  have hz' : dec n z = dec n (thd x y n) := by
    rw [dec_thd]
    funext i
    have := congrFun habc i
    simp only [Pi.add_apply] at this
    simp only [Pi.neg_apply, Pi.add_apply]
    exact hsolve _ _ _ this
  have hzy : z = thd x y n := dec_inj (hlt z hz) (thd_lt _ _ _) hz'
  have hp := congrArg (fun m => m.testBit z) (hpair x hx)
  simp only [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow] at hp
  rw [hmem z hz, testBit_refl (hlt z hz), hzy, thd_thd (hlt y hy), hmem y hy] at hp
  have hxz : x = thd x y n := by simpa using hp
  have hyx : y = x := by
    have h1 := thd_thd (x := x) (hlt y hy)
    rw [← hxz, thd_self (hlt x hx)] at h1
    exact h1.symm
  rw [hyx]

-- ## The Hill cap: the 112 vectors `±v` over the 56-cap of `PG(5,3)`, as base-3 codes.

def codes : List ℕ := [9, 10, 15, 18, 20, 21, 27, 29, 30, 41, 43, 54, 55, 60, 77, 79, 97, 104, 113, 127, 128, 129, 132, 142, 145, 146, 147, 150, 178, 185, 194, 208, 209, 210, 213, 223, 226, 227, 228, 231, 248, 250, 283, 287, 288, 290, 291, 306, 307, 312, 319, 323, 341, 346, 359, 360, 361, 363, 374, 382, 394, 396, 398, 402, 418, 431, 436, 441, 443, 447, 455, 467, 475, 477, 478, 480, 491, 493, 526, 530, 531, 533, 534, 549, 550, 555, 562, 566, 580, 593, 598, 603, 605, 609, 617, 629, 637, 639, 640, 642, 665, 670, 683, 684, 685, 687, 698, 706, 718, 720, 722, 726]

-- Bit `c` of `mask` is set exactly when `c ∈ codes`.
def mask : ℕ := 381959257184467327969796522212131884187408293884297760164932639138135952689524311199882471158717303362122032590021953719639456204551667554115024486844022542358704761006342836104175208310777513628063605508895934231381504

theorem codes_lt : ∀ c ∈ codes, c < 3 ^ 6 := by decide +kernel

theorem codes_mem : ∀ c ∈ codes, mask.testBit c = true := by decide +kernel

-- The cap test: the mask meets each of its 112 reflections only at the centre.
theorem codes_pair : ∀ x ∈ codes, mask &&& refl 6 x mask = 1 <<< x := by decide +kernel

theorem codes_chain : List.IsChain (· < ·) codes := by decide +kernel

def cap : Finset (Fin 6 → ZMod 3) := (codes.map (dec 6)).toFinset

theorem cap_free : ThreeAPFree (cap : Set (Fin 6 → ZMod 3)) :=
  threeAPFree_of_mask 6 codes mask codes_lt codes_mem codes_pair

theorem cap_card : cap.card = 112 := by
  rw [cap, List.toFinset_card_of_nodup, List.length_map]
  · rfl
  · exact List.Nodup.map_on (fun x hx y hy h => dec_inj (codes_lt x hx) (codes_lt y hy) h)
      (codes_chain.pairwise.imp fun h => Nat.ne_of_lt h)

theorem f6 : 112 ≤ SqueezeBench.CapSet.f 6 := by
  have h := SqueezeBench.CapSet.le_f_of_threeAPFree (A := cap) (by decide) cap_free
  rwa [cap_card] at h

-- ## The record: blocks of six coordinates, and the product rule of V001.

theorem key : ∀ n, 1 ≤ n → 112 ^ (n / 6) * head (n % 6) ≤ SqueezeBench.CapSet.f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hbig : 7 ≤ n
    · have hm : 1 ≤ n - 6 := by omega
      have hdiv : n / 6 = (n - 6) / 6 + 1 := by omega
      have hmod : n % 6 = (n - 6) % 6 := by omega
      have hrec := ih (n - 6) (by omega) hm
      calc 112 ^ (n / 6) * head (n % 6)
          = 112 * (112 ^ ((n - 6) / 6) * head ((n - 6) % 6)) := by
            rw [hdiv, hmod]; ring
        _ ≤ SqueezeBench.CapSet.f 6 * SqueezeBench.CapSet.f (n - 6) := Nat.mul_le_mul f6 hrec
        _ ≤ SqueezeBench.CapSet.f (6 + (n - 6)) :=
            SqueezeBench.CapSet.Lower.V001.f_mul_le 6 (n - 6) (by norm_num) hm
        _ = SqueezeBench.CapSet.f n := by rw [show 6 + (n - 6) = n from by omega]
    · interval_cases n
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f1
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f2
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f3
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f4
      · simpa [head] using SqueezeBench.CapSet.Lower.V002.f5
      · simpa [head] using f6

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f blocks :=
  SqueezeBench.pin_lowerBoundHolds fun n hn => key n (by simpa using hn)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.CapSet.Lower.V002.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.CapSet.Lower.V002.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Lower.V002.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.CapSet.nMin) (n₀ := 6) (by decide) (by decide)

end SqueezeBench.CapSet.Lower.V003
