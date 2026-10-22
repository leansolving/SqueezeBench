import SqueezeBench.Problems.HypercubeC4.Records.Lower.V008.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V007.Proof

/-! Record V008 for HypercubeC4, lower direction, by Pablo Manrique: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V008.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V008

open Finset SimpleGraph

/-! ### Words as binary numerals -/

-- The word `x` read as a binary numeral, bit `i` being `x i`.
def code : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, x => (x 0).toNat + 2 * code (fun i => x i.succ)

-- The word with bits `c.testBit 0, …, c.testBit (n-1)`.
def decode (n : ℕ) (c : ℕ) : Fin n → Bool := fun i => c.testBit i

theorem code_lt {n : ℕ} (x : Fin n → Bool) : code x < 2 ^ n := by
  induction n with
  | zero => simp [code]
  | succ n ih =>
    simp only [code, pow_succ]
    have := ih (fun i => x i.succ)
    cases x 0 <;> simp <;> omega

theorem testBit_code {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (code x).testBit k = x ⟨k, hk⟩ := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      rw [show x ⟨0, hk⟩ = x 0 from rfl]
      simp only [code, Nat.testBit_zero]
      cases x 0 <;> simp [Nat.add_mul_mod_self_left]
    | succ k =>
      rw [Nat.testBit_succ]
      have h2 : ((x 0).toNat + 2 * code (fun i => x i.succ)) / 2 = code (fun i => x i.succ) := by
        cases x 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      simp only [code]
      rw [h2, ih (fun i => x i.succ) k (by omega)]
      rfl

theorem testBit_code_of_ge {n : ℕ} (x : Fin n → Bool) {k : ℕ} (hk : n ≤ k) :
    (code x).testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (code_lt x) (Nat.pow_le_pow_right (by norm_num) hk))

theorem decode_code {n : ℕ} (x : Fin n → Bool) : decode n (code x) = x := by
  funext i
  simp only [decode]
  rw [testBit_code x i i.isLt]

theorem code_decode {n : ℕ} {c : ℕ} (hc : c < 2 ^ n) : code (decode n c) = c := by
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k n with hk | hk
  · rw [testBit_code _ k hk]; rfl
  · rw [testBit_code_of_ge _ hk]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hk))).symm

-- Flipping bit `i` is xor with `2 ^ i`.
theorem code_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    code (HypercubeC4.flip x i) = code x ^^^ 2 ^ (i : ℕ) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.lt_or_ge k n with hk | hk
  · rw [testBit_code _ k hk, testBit_code _ k hk, HypercubeC4.flip_apply]
    by_cases h : (⟨k, hk⟩ : Fin n) = i
    · have h' : (i : ℕ) = k := by rw [← h]
      simp [h, h']
    · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e.symm)
      simp [h, h']
  · rw [testBit_code_of_ge _ hk, testBit_code_of_ge _ hk]
    have : (i : ℕ) ≠ k := by have := i.isLt; omega
    simp [this]

-- Counting words by a property of their numerals.
theorem card_code {n : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    #{x : Fin n → Bool | P (code x)} = #{c ∈ range (2 ^ n) | P c} := by
  refine Finset.card_nbij' code (decode n) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_range] at hx ⊢
    exact ⟨code_lt x, hx⟩
  · intro c hc
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_range] at hc ⊢
    rw [code_decode hc.1]; exact hc.2
  · intro x _; exact decode_code x
  · intro c hc
    simp only [coe_filter, mem_range] at hc
    exact code_decode hc.1

/-! ### Popcount -/

-- The number of set bits among the low `k` bits of `m`, by structural recursion on `k`.
def pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => (m &&& 1) + pc k (m >>> 1)

theorem card_testBit_range (k m : ℕ) : #{c ∈ range k | m.testBit c = true} = pc k m := by
  induction k generalizing m with
  | zero => simp [pc]
  | succ k ih =>
    rw [Finset.card_filter, Finset.sum_range_succ', ← Finset.card_filter]
    simp only [pc]
    have h1 : ∀ c, m.testBit (c + 1) = (m >>> 1).testBit c := fun c => by
      rw [Nat.testBit_shiftRight, Nat.add_comm]
    simp only [h1, ih]
    rw [Nat.and_one_is_mod, Nat.testBit_zero, Nat.add_comm]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]

/-! ### The subgraph given by bitmasks -/

section Mask

variable {n : ℕ} (M : Fin n → ℕ)

-- The subgraph of `Qₙ` keeping the edge `{x, x with bit i flipped}` when bit `code x` and bit
-- `code (flip x i)` of `M i` are both set.
def mgraph : SimpleGraph (Fin n → Bool) where
  Adj x y := ∃ i, y = HypercubeC4.flip x i ∧ (M i).testBit (code x) = true ∧
    (M i).testBit (code y) = true
  symm := ⟨fun x y ⟨i, hy, hx, hy'⟩ => ⟨i, by rw [hy, HypercubeC4.flip_flip], hy', hx⟩⟩
  loopless := ⟨fun x ⟨i, h, _⟩ => by
    have := congrFun h i
    rw [HypercubeC4.flip_apply, if_pos rfl] at this
    cases x i <;> simp at this⟩

instance decMgraph : DecidableRel (mgraph M).Adj := fun x y =>
  inferInstanceAs (Decidable (∃ i, y = HypercubeC4.flip x i ∧ (M i).testBit (code x) = true ∧
    (M i).testBit (code y) = true))

theorem mgraph_le : mgraph M ≤ HypercubeC4.hypercube n := fun _ _ ⟨i, hy, _, _⟩ =>
  HypercubeC4.hypercube_adj_iff.mpr ⟨i, hy⟩

theorem mgraph_adj_flip (x : Fin n → Bool) (i : Fin n) :
    (mgraph M).Adj x (HypercubeC4.flip x i) ↔
      (M i).testBit (code x) = true ∧ (M i).testBit (code x ^^^ 2 ^ (i : ℕ)) = true := by
  rw [← code_flip]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    have hij : i = j := V001.flip_inj x hj
    subst hij
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨i, rfl, h1, h2⟩

-- No square survives when no square of the masks is all set.
theorem mgraph_not_hasSquare
    (hsq : ∀ c, c < 2 ^ n → ∀ i j : Fin n, i ≠ j →
      ¬ ((M i).testBit c = true ∧ (M j).testBit c = true ∧
        (M i).testBit (c ^^^ 2 ^ (j : ℕ)) = true ∧ (M j).testBit (c ^^^ 2 ^ (i : ℕ)) = true)) :
    ¬ HypercubeC4.HasSquare (mgraph M) := by
  rintro ⟨x, i, j, hij, h1, h2, h3, h4⟩
  rw [mgraph_adj_flip] at h1 h2 h3
  rw [V005.flip_comm x hij, mgraph_adj_flip] at h4
  rw [code_flip] at h3 h4
  exact hsq (code x) (code_lt x) i j hij ⟨h1.1, h2.1, h4.1, h3.1⟩

theorem mgraph_degree (x : Fin n → Bool) :
    (mgraph M).degree x = #{i | (M i).testBit (code x) = true ∧
      (M i).testBit (code x ^^^ 2 ^ (i : ℕ)) = true} := by
  rw [← card_neighborFinset_eq_degree]
  have : (mgraph M).neighborFinset x =
      (univ.filter fun i => (M i).testBit (code x) = true ∧
        (M i).testBit (code x ^^^ 2 ^ (i : ℕ)) = true).image (HypercubeC4.flip x) := by
    ext y
    simp only [mem_neighborFinset, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl, h⟩
      exact ⟨i, (mgraph_adj_flip M x i).mp ⟨i, rfl, h⟩, rfl⟩
    · rintro ⟨i, h, rfl⟩
      exact (mgraph_adj_flip M x i).mpr h
  rw [this, card_image_of_injective _ (fun i j h => V001.flip_inj x h)]

-- With symmetric masks, twice the number of edges is the sum of the popcounts.
theorem mgraph_two_mul_card_edges
    (hsym : ∀ c, c < 2 ^ n → ∀ i : Fin n, (M i).testBit (c ^^^ 2 ^ (i : ℕ)) = (M i).testBit c) :
    2 * #(mgraph M).edgeFinset = ∑ i, pc (2 ^ n) (M i) := by
  rw [← sum_degrees_eq_twice_card_edges]
  have h1 : ∀ x : Fin n → Bool, (mgraph M).degree x = #{i | (M i).testBit (code x) = true} := by
    intro x
    rw [mgraph_degree]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, hsym (code x) (code_lt x) i, and_self]
  simp only [h1]
  rw [V007.sum_card_swap (fun x i => (M i).testBit (code x) = true)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [card_code (fun c => (M i).testBit c = true), card_testBit_range]

end Mask

/-! ### Xor with a power of two is adding or subtracting it -/

theorem lt_two_pow_of_testBit_false {r j : ℕ} (hr : r < 2 ^ (j + 1)) (h : r.testBit j = false) :
    r < 2 ^ j := by
  by_contra hge
  push Not at hge
  have e : r = 2 ^ j + (r - 2 ^ j) := by omega
  have hlt : r - 2 ^ j < 2 ^ j := by rw [pow_succ] at hr; omega
  rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt] at h
  simp at h

theorem xor_two_pow_of_testBit_false {c j : ℕ} (h : c.testBit j = false) :
    c ^^^ 2 ^ j = c + 2 ^ j := by
  have hdecomp : c = 2 ^ (j + 1) * (c / 2 ^ (j + 1)) + c % 2 ^ (j + 1) := (Nat.div_add_mod c _).symm
  have hr : c % 2 ^ (j + 1) < 2 ^ (j + 1) := Nat.mod_lt _ (by positivity)
  have hrj : (c % 2 ^ (j + 1)).testBit j = false := by
    rw [Nat.testBit_mod_two_pow]; simp [h]
  have hr' : c % 2 ^ (j + 1) < 2 ^ j := lt_two_pow_of_testBit_false hr hrj
  generalize c / 2 ^ (j + 1) = q at hdecomp
  generalize c % 2 ^ (j + 1) = r at hdecomp hr hrj hr'
  subst hdecomp
  -- everything is an `or` of disjoint pieces
  have e1 : 2 ^ (j + 1) * q + r = 2 ^ (j + 1) * q ||| r := Nat.two_pow_add_eq_or_of_lt hr q
  have e2 : 2 ^ (j + 1) * q + r + 2 ^ j = 2 ^ (j + 1) * q ||| (2 ^ j * 1 + r) := by
    rw [← Nat.two_pow_add_eq_or_of_lt (i := j + 1) (b := 2 ^ j * 1 + r) (by rw [pow_succ]; omega) q]
    ring
  have e3 : 2 ^ j * 1 + r = 2 ^ j * 1 ||| r := Nat.two_pow_add_eq_or_of_lt hr' 1
  rw [e2, e3, Nat.mul_one, e1]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor, Nat.testBit_lor, Nat.testBit_two_pow, Nat.testBit_two_pow_mul]
  by_cases hk : j = k
  · subst hk
    have h1 : r.testBit j = false := Nat.testBit_lt_two_pow hr'
    have h2 : ¬ (j ≥ j + 1) := by omega
    simp [h1, h2]
  · simp [hk]

theorem xor_two_pow_of_testBit_true {c j : ℕ} (h : c.testBit j = true) :
    c ^^^ 2 ^ j = c - 2 ^ j := by
  have hge : 2 ^ j ≤ c := Nat.ge_two_pow_of_testBit h
  have h' : (c - 2 ^ j).testBit j = false := by
    have := Nat.testBit_two_pow_add_eq (c - 2 ^ j) j
    rw [show 2 ^ j + (c - 2 ^ j) = c by omega, h] at this
    cases hb : (c - 2 ^ j).testBit j
    · rfl
    · rw [hb] at this; exact absurd this (by decide)
  have := xor_two_pow_of_testBit_false h'
  rw [show c - 2 ^ j + 2 ^ j = c by omega] at this
  calc c ^^^ 2 ^ j = ((c - 2 ^ j) ^^^ 2 ^ j) ^^^ 2 ^ j := by rw [this]
    _ = c - 2 ^ j := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

-- Bit `j` of `c - 2^j` is the opposite of bit `j` of `c`, when `2^j ≤ c`.
theorem testBit_sub_two_pow {c j : ℕ} (hge : 2 ^ j ≤ c) :
    (c - 2 ^ j).testBit j = !c.testBit j := by
  have := Nat.testBit_two_pow_add_eq (c - 2 ^ j) j
  rw [show 2 ^ j + (c - 2 ^ j) = c by omega] at this
  rw [this, Bool.not_not]

/-! ### The mask of positions with a clear bit, and the bit permutation `c ↦ c ^^^ 2^j` -/

-- The number whose set bits are the positions `c < 2^n` with bit `j` clear.
def A : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, j => if j = n then 2 ^ 2 ^ n - 1 else A n j ||| (A n j <<< 2 ^ n)

theorem testBit_A (n j c : ℕ) : (A n j).testBit c = (decide (c < 2 ^ n) && !c.testBit j) := by
  induction n generalizing c with
  | zero =>
    simp only [A, pow_zero]
    rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · simp [show ¬ (0 = c) by omega, show ¬ c < 1 by omega]
  | succ n ih =>
    simp only [A]
    split_ifs with hj
    · rw [hj, Nat.testBit_two_pow_sub_one]
      by_cases hc : c < 2 ^ n
      · have hc2 : c < 2 ^ (n + 1) := by rw [pow_succ]; omega
        simp [hc, hc2, Nat.testBit_lt_two_pow hc]
      · by_cases hc2 : c < 2 ^ (n + 1)
        · have hlt : c - 2 ^ n < 2 ^ n := by rw [pow_succ] at hc2; omega
          have hb : c.testBit n = true := by
            have e : c = 2 ^ n + (c - 2 ^ n) := by omega
            rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; rfl
          simp [hc, hc2, hb]
        · simp [hc, hc2]
    · rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih, ih]
      by_cases hc : c < 2 ^ n
      · have hc2 : c < 2 ^ (n + 1) := by rw [pow_succ]; omega
        simp [hc, hc2, show ¬ (c ≥ 2 ^ n) by omega]
      · by_cases hc2 : c < 2 ^ (n + 1)
        · have hge : c ≥ 2 ^ n := by omega
          have hlt : c - 2 ^ n < 2 ^ n := by rw [pow_succ] at hc2; omega
          have hb : c.testBit j = (c - 2 ^ n).testBit j := by
            have e : c = 2 ^ n * 1 + (c - 2 ^ n) := by omega
            conv_lhs => rw [e]
            rw [Nat.testBit_two_pow_mul_add 1 hlt j]
            split_ifs with hjn
            · rfl
            · have hjn' : n < j := by omega
              rw [Nat.testBit_lt_two_pow
                (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hjn'.le))]
              rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
              simp; omega
          simp [hc, hc2, hge, hlt, hb]
        · have : ¬ (c - 2 ^ n < 2 ^ n) := by rw [pow_succ] at hc2; omega
          simp [hc, hc2, this]

-- Bit `c` of `sw n j M` is bit `c ^^^ 2^j` of `M` (for `c < 2^n`, `j < n`).
def sw (n j M : ℕ) : ℕ := ((M >>> 2 ^ j) &&& A n j) ||| ((M &&& A n j) <<< 2 ^ j)

theorem testBit_sw {n j c : ℕ} (hc : c < 2 ^ n) (M : ℕ) :
    (sw n j M).testBit c = M.testBit (c ^^^ 2 ^ j) := by
  unfold sw
  rw [Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftLeft, Nat.testBit_land,
    Nat.testBit_shiftRight, testBit_A, testBit_A]
  by_cases hb : c.testBit j = true
  · rw [xor_two_pow_of_testBit_true hb]
    have hge : 2 ^ j ≤ c := Nat.ge_two_pow_of_testBit hb
    have hb' : (c - 2 ^ j).testBit j = false := by rw [testBit_sub_two_pow hge, hb]; rfl
    have hlt : c - 2 ^ j < 2 ^ n := lt_of_le_of_lt (Nat.sub_le c _) hc
    simp [hb, hb', hge, hc, hlt]
  · rw [Bool.not_eq_true] at hb
    rw [xor_two_pow_of_testBit_false hb, Nat.add_comm]
    by_cases hge : 2 ^ j ≤ c
    · have hb' : (c - 2 ^ j).testBit j = true := by rw [testBit_sub_two_pow hge, hb]; rfl
      simp [hb, hb', hge, hc]
    · simp [hb, hc, hge]

/-! ### Certificates by bitmask arithmetic -/

section Cert

variable {n : ℕ} (M : Fin n → ℕ)

theorem mgraph_not_hasSquare_sw
    (hsq : ∀ i j : Fin n, i ≠ j → M i &&& M j &&& sw n j (M i) &&& sw n i (M j) = 0) :
    ¬ HypercubeC4.HasSquare (mgraph M) := by
  refine mgraph_not_hasSquare M fun c hc i j hij ⟨h1, h2, h3, h4⟩ => ?_
  have h := congrArg (fun m => m.testBit c) (hsq i j hij)
  simp only [Nat.testBit_land, Nat.zero_testBit, testBit_sw hc,
    h1, h2, h3, h4, Bool.and_self] at h
  simp at h

theorem mgraph_two_mul_card_edges_sw (hsym : ∀ i : Fin n, sw n i (M i) = M i) :
    2 * #(mgraph M).edgeFinset = ∑ i, pc (2 ^ n) (M i) := by
  refine mgraph_two_mul_card_edges M fun c hc i => ?_
  rw [← testBit_sw hc, hsym i]

end Cert


/-! ### The 682-edge subgraph of `Q₈` -/

-- Bit `c` of `M i` is set iff the edge from vertex `c` in direction `i` is kept (256 vertices, so 256 bits per mask).
-- Each edge is stored from both ends, hence `M8_sym`; `M8_sq` says no square keeps all four edges; `M8_count` gives 2 · 682.
def M0 : ℕ := 0xc00c03ff03fff3cf3f3ffcfcfc0c0cf3ffcff3f3f300cffc3c30ff0fcffff3cf
def M1 : ℕ := 0xfa5f5fa55fa5affaf5faafafaf5f5fa055f5afafaf5af55f0ff5a55afaa5aff5
def M2 : ℕ := 0xddeebb55bb55dd77eedd777777eeee1166bbddddddaabb44ffbb55008855ddbb
def M3 : ℕ := 0x1d1dfefefefe8d8d6a6a9696f9f9ffffb9b96969f7f7bbbb5e5ef5f58a8a7e7e
def M4 : ℕ := 0xe7fbe7fbf67af67adbd8dbd806ff06ff517e517e7ecd7ecdebbfebbf7d767d76
def M5 : ℕ := 0xe7fb0985e7fb0985dbb7f96fdbb7f96fae1f7e53ae1f7e53f7dc9eeaf7dc9eea
def M6 : ℕ := 0x3fb7fc6bfc04f37e3fb7fc6bfc04f37edbc39efd7dff81bbdbc39efd7dff81bb
def M7 : ℕ := 0xbfe4f69e09ff7eb7a46f6bf777fbf38dbfe4f69e09ff7eb7a46f6bf777fbf38d

def M8 : Fin 8 → ℕ := ![M0, M1, M2, M3, M4, M5, M6, M7]

theorem M8_sq : ∀ i j : Fin 8, i ≠ j → M8 i &&& M8 j &&& sw 8 j (M8 i) &&& sw 8 i (M8 j) = 0 := by
  decide +kernel

theorem M8_sym : ∀ i : Fin 8, sw 8 i (M8 i) = M8 i := by
  decide +kernel

theorem M8_count : ∑ i, pc (2 ^ 8) (M8 i) = 2 * 682 := by
  rw [Fin.sum_univ_eight]
  decide +kernel

-- Proved for an arbitrary certificate `M` and then instantiated, so the edge count is never a closed term (nanoda would count the edges by evaluation).
theorem le_f_eight_of (M : Fin 8 → ℕ) (hsym : ∀ i : Fin 8, sw 8 i (M i) = M i)
    (hsq : ∀ i j : Fin 8, i ≠ j → M i &&& M j &&& sw 8 j (M i) &&& sw 8 i (M j) = 0)
    (hc : ∑ i, pc (2 ^ 8) (M i) = 2 * 682) : 682 ≤ SqueezeBench.HypercubeC4.f 8 := by
  have h := mgraph_two_mul_card_edges_sw M hsym
  rw [hc] at h
  have h2 : #(mgraph M).edgeFinset = 682 := by omega
  rw [← h2]
  exact HypercubeC4.le_f_of_not_hasSquare (by rw [HypercubeC4.nMin_eq]; omega) (mgraph_le M)
    (mgraph_not_hasSquare_sw M hsq)

theorem le_f_eight : 682 ≤ SqueezeBench.HypercubeC4.f 8 := le_f_eight_of M8 M8_sym M8_sq M8_count

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.patch_valid SqueezeBench.HypercubeC4.Lower.V007.valid le_f_eight

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V007.record record :=
  SqueezeBench.patch_improves (by decide +kernel)

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V007.record record :=
  SqueezeBench.patch_strict (by decide) (by decide +kernel)

end SqueezeBench.HypercubeC4.Lower.V008
