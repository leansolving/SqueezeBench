import SqueezeBench.Problems.CapSet.Records.Upper.V008.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V007.Proof

/-! Record V008 for CapSet, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V008.lean`.

The hyperplane recursion of Bierbrauer–Edel and Davis–Maclagan: if every hyperplane section
of a cap `A ⊆ F₃ⁿ` has at most `h` points, then `|A| (3ⁿ + 3h) ≤ 3ⁿ (3h + 1)`. The proof
double-counts, over all nonzero directions `r`, the sizes `a, b, c` of the three parallel
sections `{x ∈ A : r ⬝ᵥ x = t}`: the sums of `a`, `a²` and `a³` are determined by `|A|` alone
(every pair of points lies in `3^(n-1) - 1` nonzero directions, every non-collinear triple in
`3^(n-2) - 1`), while `9 Σa³ − 9|A| Σa² + 2|A|³ + (3h − |A|)(3 Σa² − |A|²)` is
`3 Σ (h−a)(b−c)² ≥ 0` for each direction. With the sections of a cap in `F₃⁴` bounded by
`f 3 = 9` this gives `f 4 ≤ 21`, and the equality case (every direction of type `(7,7,7)` or
`(9,9,3)`, a parity count) excludes `21`. Iterating from `f 4 ≤ 20` gives `⌊3ⁿ/n⌋`-like bounds. -/

namespace SqueezeBench.CapSet.Upper.V008

open SqueezeBench Finset

variable {n : ℕ}


theorem zmod3_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by revert a; decide

theorem univ_zmod3 : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide

theorem sum_zmod3 {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) : ∑ t, f t = f 0 + f 1 + f 2 := by
  rw [univ_zmod3, sum_insert (by decide), sum_insert (by decide), sum_singleton, add_assoc]

-- Fibres of `φ` on a set `S` closed under `+ u`, where `φ (r + u) = φ r + 1`, have equal sizes.
theorem card_fiber_succ (S : Finset (Fin n → ZMod 3)) (u : Fin n → ZMod 3)
    (hS : ∀ r ∈ S, r + u ∈ S) (φ : (Fin n → ZMod 3) → ZMod 3) (hφ : ∀ r, φ (r + u) = φ r + 1)
    (t : ZMod 3) :
    (S.filter (fun r => φ r = t)).card = (S.filter (fun r => φ r = t + 1)).card := by
  classical
  have h3 : ∀ a : ZMod 3, a + 1 + 1 + 1 = a := by decide
  apply le_antisymm
  · calc (S.filter (fun r => φ r = t)).card
        = ((S.filter (fun r => φ r = t)).image (· + u)).card :=
          (card_image_of_injective _ (add_left_injective u)).symm
      _ ≤ (S.filter (fun r => φ r = t + 1)).card := by
          apply card_le_card
          intro y hy
          rw [mem_image] at hy
          obtain ⟨r, hr, rfl⟩ := hy
          rw [mem_filter] at hr ⊢
          exact ⟨hS r hr.1, by rw [hφ, hr.2]⟩
  · calc (S.filter (fun r => φ r = t + 1)).card
        = ((S.filter (fun r => φ r = t + 1)).image (· + (u + u))).card :=
          (card_image_of_injective _ (add_left_injective _)).symm
      _ ≤ (S.filter (fun r => φ r = t)).card := by
          apply card_le_card
          intro y hy
          rw [mem_image] at hy
          obtain ⟨r, hr, rfl⟩ := hy
          rw [mem_filter] at hr ⊢
          refine ⟨?_, ?_⟩
          · rw [← add_assoc]; exact hS _ (hS r hr.1)
          · rw [← add_assoc, hφ, hφ, hr.2]; exact h3 t

theorem card_fiber_third (S : Finset (Fin n → ZMod 3)) (u : Fin n → ZMod 3)
    (hS : ∀ r ∈ S, r + u ∈ S) (φ : (Fin n → ZMod 3) → ZMod 3) (hφ : ∀ r, φ (r + u) = φ r + 1)
    (t : ZMod 3) :
    3 * (S.filter (fun r => φ r = t)).card = S.card := by
  classical
  have h01 := card_fiber_succ S u hS φ hφ 0
  have h12 := card_fiber_succ S u hS φ hφ 1
  have hsum := card_eq_sum_card_fiberwise (f := φ) (s := S) (t := (univ : Finset (ZMod 3)))
    (fun _ _ => mem_univ _)
  rw [sum_zmod3] at hsum
  norm_num at h01 h12
  rcases zmod3_cases t with rfl | rfl | rfl <;> omega

theorem card_fun : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by simp

-- For `v ≠ 0`, each level set of `r ↦ r ⬝ᵥ v` has `3 ^ n / 3` points.
theorem card_dot_eq {v : Fin n → ZMod 3} (hv : v ≠ 0) (t : ZMod 3) :
    3 * ((univ : Finset (Fin n → ZMod 3)).filter (fun r => r ⬝ᵥ v = t)).card = 3 ^ n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hsq : v i * v i = 1 := by
    generalize v i = a at hi ⊢; revert a; decide
  have := card_fiber_third univ (Pi.single i (v i)) (fun _ _ => mem_univ _) (fun r => r ⬝ᵥ v)
    (fun r => by rw [add_dotProduct, single_dotProduct, hsq]) t
  rw [this, card_univ, card_fun]

-- Two vectors `v, w` with `w ∉ {0, v, -v}` admit `u` with `u ⬝ᵥ v = 0` and `u ⬝ᵥ w = 1`.
theorem exists_dot_zero_one {v w : Fin n → ZMod 3} (hv : v ≠ 0) (hw0 : w ≠ 0) (hw1 : w ≠ v)
    (hw2 : w ≠ -v) : ∃ u, u ⬝ᵥ v = 0 ∧ u ⬝ᵥ w = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : ∀ u, u ⬝ᵥ v = 0 → u ⬝ᵥ w = 0 := by
    intro u hu
    have h1 := hcon u hu
    have h2 := hcon (u + u) (by rw [add_dotProduct, hu, add_zero])
    rw [add_dotProduct] at h2
    generalize u ⬝ᵥ w = a at h1 h2 ⊢
    revert a; decide
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hsq : v i * v i = 1 := by generalize v i = a at hi ⊢; revert a; decide
  have hprop : ∀ j, v i * w j = v j * w i := by
    intro j
    have := hzero (Pi.single j (v i) - Pi.single i (v j)) (by
      rw [sub_dotProduct, single_dotProduct, single_dotProduct]; ring)
    rw [sub_dotProduct, single_dotProduct, single_dotProduct] at this
    linear_combination this
  have hw : w = (w i * v i) • v := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    have := hprop j
    linear_combination (v i) * this - (w j) * hsq
  have hneg : ∀ x : Fin n → ZMod 3, (2 : ZMod 3) • x = -x := by
    intro x; funext j; rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    generalize x j = a; revert a; decide
  rcases zmod3_cases (w i * v i) with h | h | h <;> rw [h] at hw
  · exact hw0 (by rw [hw, zero_smul])
  · exact hw1 (by rw [hw, one_smul])
  · exact hw2 (by rw [hw, hneg])

-- For `v ≠ 0` and `w ∉ {0, v, -v}`, the common zero set has `3 ^ n / 9` points.
theorem card_dot_dot_eq {v w : Fin n → ZMod 3} (hv : v ≠ 0) (hw0 : w ≠ 0) (hw1 : w ≠ v)
    (hw2 : w ≠ -v) :
    9 * ((univ : Finset (Fin n → ZMod 3)).filter (fun r => r ⬝ᵥ v = 0 ∧ r ⬝ᵥ w = 0)).card
      = 3 ^ n := by
  classical
  obtain ⟨u, huv, huw⟩ := exists_dot_zero_one hv hw0 hw1 hw2
  have h1 := card_fiber_third (univ.filter (fun r => r ⬝ᵥ v = 0)) u
    (fun r hr => by
      rw [mem_filter] at hr ⊢
      exact ⟨mem_univ _, by rw [add_dotProduct, hr.2, huv, add_zero]⟩)
    (fun r => r ⬝ᵥ w) (fun r => by rw [add_dotProduct, huw]) 0
  rw [filter_filter] at h1
  have h2 := card_dot_eq hv 0
  omega


-- Size of the hyperplane section `{x ∈ A : r ⬝ᵥ x = t}`.
def sec (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) (t : ZMod 3) : ℕ :=
  (A.filter (fun x => r ⬝ᵥ x = t)).card

theorem sum_sec (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) :
    ∑ t : ZMod 3, sec A r t = A.card := by
  classical
  unfold sec
  exact (card_eq_sum_card_fiberwise (f := fun x => r ⬝ᵥ x) (t := (univ : Finset (ZMod 3)))
    (fun _ _ => mem_univ _)).symm

theorem ind2 (a b : ZMod 3) :
    ∑ t : ZMod 3, ((if a = t then 1 else 0) * (if b = t then 1 else 0) : ℕ)
      = if a = b then 1 else 0 := by
  revert a b; decide

theorem ind3 (a b c : ZMod 3) :
    ∑ t : ZMod 3, ((if a = t then 1 else 0) * (if b = t then 1 else 0) * (if c = t then 1 else 0) : ℕ)
      = if a = b ∧ b = c then 1 else 0 := by
  revert a b c; decide

theorem sum_sec_sq (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) :
    ∑ t : ZMod 3, (sec A r t) ^ 2
      = ∑ x ∈ A, ∑ y ∈ A, if r ⬝ᵥ x = r ⬝ᵥ y then 1 else 0 := by
  classical
  unfold sec
  simp only [card_filter, sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  exact ind2 _ _

theorem sum_sec_cube (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) :
    ∑ t : ZMod 3, (sec A r t) ^ 3
      = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, if r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ z then 1 else 0 := by
  classical
  have h1 : ∀ t, (sec A r t) ^ 3 = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
      (if r ⬝ᵥ x = t then 1 else 0) * (if r ⬝ᵥ y = t then 1 else 0)
        * (if r ⬝ᵥ z = t then 1 else 0) := by
    intro t
    unfold sec
    rw [card_filter, pow_three', sum_mul_sum, sum_mul_sum]
    simp only [Finset.sum_mul]
    exact sum_congr rfl (fun x _ => sum_comm)
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun z _ => ?_)
  exact ind3 _ _ _

-- Number of nonzero `r` with `r ⬝ᵥ x = r ⬝ᵥ y`, plus one.
theorem card_pair {m : ℕ} (x y : Fin (m + 2) → ZMod 3) :
    ((univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y)).card + 1
      = 3 * 3 ^ m + if x = y then 6 * 3 ^ m else 0 := by
  classical
  have hins : (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ⬝ᵥ x = r ⬝ᵥ y)
      = insert 0 (univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y)) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hr : r = 0
    · subst hr; simp
    · simp [hr]
  have hcard : (univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y)).card + 1
      = ((univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ⬝ᵥ x = r ⬝ᵥ y)).card := by
    rw [hins, card_insert_of_notMem (by simp)]
  rw [hcard]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have : (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ⬝ᵥ x = r ⬝ᵥ x) = univ :=
      filter_true_of_mem (fun _ _ => rfl)
    rw [this, card_univ, card_fun]
    ring
  · rw [if_neg hxy, add_zero]
    have hv : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have h := card_dot_eq hv 0
    have hfilt : (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ⬝ᵥ x = r ⬝ᵥ y)
        = univ.filter (fun r => r ⬝ᵥ (x - y) = 0) := by
      ext r; simp only [mem_filter, mem_univ, true_and, dotProduct_sub, sub_eq_zero]
    rw [hfilt]
    have : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
    omega

-- Number of nonzero `r` with `r ⬝ᵥ x = r ⬝ᵥ y = r ⬝ᵥ z`, plus one, for three points of a cap.
theorem card_triple {m : ℕ} {A : Finset (Fin (m + 2) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 2) → ZMod 3))) {x y z : Fin (m + 2) → ZMod 3}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) :
    ((univ : Finset (Fin (m + 2) → ZMod 3)).filter
        (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ z))).card + 1
      = 3 ^ m + 2 * 3 ^ m * ((if x = y then 1 else 0) + (if y = z then 1 else 0)
          + (if x = z then 1 else 0)) + 2 * 3 ^ m * (if x = y ∧ y = z then 1 else 0) := by
  classical
  by_cases hxy : x = y
  · subst hxy
    have hfilt : (univ : Finset (Fin (m + 2) → ZMod 3)).filter
        (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ x ∧ r ⬝ᵥ x = r ⬝ᵥ z))
        = univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ z) := by
      ext r; simp
    rw [hfilt, if_pos rfl]
    have h := card_pair x z
    by_cases hxz : x = z
    · subst hxz
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      rw [if_pos rfl] at h
      omega
    · rw [if_neg hxz, if_neg (fun h' => hxz h'.2)]
      rw [if_neg hxz] at h
      omega
  by_cases hyz : y = z
  · subst hyz
    have hfilt : (univ : Finset (Fin (m + 2) → ZMod 3)).filter
        (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ y))
        = univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y) := by
      ext r; simp
    rw [hfilt, if_neg hxy, if_pos rfl, if_neg (fun h' => hxy h'.1)]
    have h := card_pair x y
    rw [if_neg hxy] at h
    omega
  by_cases hxz : x = z
  · subst hxz
    have hfilt : (univ : Finset (Fin (m + 2) → ZMod 3)).filter
        (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ x))
        = univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y) := by
      ext r
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h2.symm⟩
    rw [hfilt, if_neg hxy, if_neg hyz, if_pos rfl, if_neg (fun h' => hxy h'.1)]
    have h := card_pair x y
    rw [if_neg hxy] at h
    omega
  -- all distinct: `x - y` and `y - z` are independent since the three points are not collinear
  rw [if_neg hxy, if_neg hyz, if_neg hxz, if_neg (fun h' => hxy h'.1)]
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hw0 : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hw1 : y - z ≠ x - y := by
    intro h
    apply hxy
    exact hA (mem_coe.mpr hx) (mem_coe.mpr hy) (mem_coe.mpr hz) (by linear_combination -h)
  have hw2 : y - z ≠ -(x - y) := by
    intro h
    apply hxz
    linear_combination h
  have h9 := card_dot_dot_eq hv hw0 hw1 hw2
  have hins : (univ : Finset (Fin (m + 2) → ZMod 3)).filter
      (fun r => r ⬝ᵥ (x - y) = 0 ∧ r ⬝ᵥ (y - z) = 0)
      = insert 0 (univ.filter (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ z))) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_insert, dotProduct_sub, sub_eq_zero]
    by_cases hr : r = 0
    · subst hr; simp
    · simp [hr]
  rw [hins, card_insert_of_notMem (by simp)] at h9
  have : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
  omega

-- Second and third moments of the hyperplane sections, per point.
def c2 (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) : ℕ := ∑ t : ZMod 3, (sec A r t) ^ 2
def c3 (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) : ℕ := ∑ t : ZMod 3, (sec A r t) ^ 3

theorem sum_sum_ite {α : Type*} [DecidableEq α] (A : Finset α) (c : ℕ) :
    ∑ x ∈ A, ∑ y ∈ A, (if x = y then c else 0) = A.card * c := by
  have : ∀ x ∈ A, ∑ y ∈ A, (if x = y then c else 0) = c := by
    intro x hx
    rw [Finset.sum_ite_eq, if_pos hx]
  rw [sum_congr rfl this, sum_const, smul_eq_mul]

theorem tsum_yz {α : Type*} [DecidableEq α] (A : Finset α) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if y = z then (1 : ℕ) else 0) = A.card * A.card := by
  have : ∀ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if y = z then (1 : ℕ) else 0) = A.card := by
    intro x _
    rw [sum_sum_ite, mul_one]
  rw [sum_congr rfl this, sum_const, smul_eq_mul]

theorem tsum_xz {α : Type*} [DecidableEq α] (A : Finset α) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if x = z then (1 : ℕ) else 0) = A.card * A.card := by
  have : ∀ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if x = z then (1 : ℕ) else 0) = A.card := by
    intro x hx
    have h2 : ∀ y ∈ A, ∑ z ∈ A, (if x = z then (1 : ℕ) else 0) = 1 := by
      intro y _
      rw [Finset.sum_ite_eq, if_pos hx]
    rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_one]
  rw [sum_congr rfl this, sum_const, smul_eq_mul]

theorem tsum_xy {α : Type*} [DecidableEq α] (A : Finset α) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if x = y then (1 : ℕ) else 0) = A.card * A.card := by
  simp only [sum_const, smul_eq_mul, ← Finset.mul_sum]
  rw [sum_sum_ite, mul_one]

theorem tsum_xyz {α : Type*} [DecidableEq α] (A : Finset α) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if x = y ∧ y = z then (1 : ℕ) else 0) = A.card := by
  have : ∀ x ∈ A, ∀ y ∈ A, ∑ z ∈ A, (if x = y ∧ y = z then (1 : ℕ) else 0)
      = if x = y then 1 else 0 := by
    intro x _ y hy
    by_cases hxy : x = y
    · subst hxy
      simp only [true_and, if_true]
      rw [Finset.sum_ite_eq, if_pos hy]
    · simp only [hxy, false_and, if_false, sum_const_zero]
  rw [sum_congr rfl (fun x hx => sum_congr rfl (fun y hy => this x hx y hy)), sum_sum_ite, mul_one]

theorem moment2 {m : ℕ} (A : Finset (Fin (m + 2) → ZMod 3)) :
    ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), c2 A r + A.card ^ 2
      = 3 * 3 ^ m * A.card ^ 2 + 6 * 3 ^ m * A.card := by
  classical
  have e1 : ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), c2 A r
      = ∑ x ∈ A, ∑ y ∈ A, (univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y)).card := by
    simp only [c2, sum_sec_sq]
    rw [sum_comm]
    refine sum_congr rfl (fun x _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun y _ => ?_)
    rw [← card_filter, filter_filter]
  have e2 : ∑ x ∈ A, ∑ y ∈ A, ((univ.filter (fun r => r ≠ 0 ∧ r ⬝ᵥ x = r ⬝ᵥ y)).card + 1)
      = ∑ x ∈ A, ∑ y ∈ A, (3 * 3 ^ m + if x = y then 6 * 3 ^ m else 0) :=
    sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => card_pair x y))
  simp only [sum_add_distrib, sum_const, smul_eq_mul, sum_sum_ite] at e2
  rw [e1]
  nlinarith [e2]

theorem moment3 {m : ℕ} {A : Finset (Fin (m + 2) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 2) → ZMod 3))) :
    ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), c3 A r + A.card ^ 3
      = 3 ^ m * A.card ^ 3 + 6 * 3 ^ m * A.card ^ 2 + 2 * 3 ^ m * A.card := by
  classical
  have e1 : ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), c3 A r
      = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
        (univ.filter (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ z))).card := by
    simp only [c3, sum_sec_cube]
    rw [sum_comm]
    refine sum_congr rfl (fun x _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun y _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun z _ => ?_)
    rw [← card_filter, filter_filter]
  have e2 : ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
        ((univ.filter (fun r => r ≠ 0 ∧ (r ⬝ᵥ x = r ⬝ᵥ y ∧ r ⬝ᵥ y = r ⬝ᵥ z))).card + 1)
      = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (3 ^ m + 2 * 3 ^ m * ((if x = y then 1 else 0)
          + (if y = z then 1 else 0) + (if x = z then 1 else 0))
          + 2 * 3 ^ m * (if x = y ∧ y = z then 1 else 0)) :=
    sum_congr rfl (fun x hx => sum_congr rfl (fun y hy => sum_congr rfl
      (fun z hz => card_triple hA hx hy hz)))
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_add, ← Finset.mul_sum, tsum_xy, tsum_yz,
    tsum_xz, tsum_xyz, sum_sum_ite, mul_one] at e2
  rw [e1]
  nlinarith [e2]

-- The per-direction inequality: with sections `a, b, c ≤ h` summing to `s`,
-- `9 Σa³ − 9 s Σa² + 2 s³ + (3h − s)(3 Σa² − s²) = 3 Σ (h−a)(b−c)² ≥ 0`.
theorem local_ineq (a b c h : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hah : a ≤ h) (hbh : b ≤ h) (hch : c ≤ h) :
    0 ≤ 9 * (a ^ 3 + b ^ 3 + c ^ 3) - 9 * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)
      + 2 * (a + b + c) ^ 3
      + (3 * h - (a + b + c)) * (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) := by
  have key : 9 * (a ^ 3 + b ^ 3 + c ^ 3) - 9 * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)
      + 2 * (a + b + c) ^ 3
      + (3 * h - (a + b + c)) * (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2)
      = 3 * ((h - a) * (b - c) ^ 2 + (h - b) * (c - a) ^ 2 + (h - c) * (a - b) ^ 2) := by ring
  rw [key]
  have h1 : 0 ≤ (h - a) * (b - c) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (h - b) * (c - a) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (h - c) * (a - b) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

-- The per-direction expression, in `ℤ`.
def E (A : Finset (Fin n → ZMod 3)) (h : ℕ) (r : Fin n → ZMod 3) : ℤ :=
  9 * (c3 A r : ℤ) - 9 * (A.card : ℤ) * (c2 A r : ℤ) + 2 * (A.card : ℤ) ^ 3
    + (3 * (h : ℤ) - A.card) * (3 * (c2 A r : ℤ) - (A.card : ℤ) ^ 2)

theorem E_eq (A : Finset (Fin n → ZMod 3)) (h : ℕ) (r : Fin n → ZMod 3) :
    E A h r = 3 * (((h : ℤ) - sec A r 0) * ((sec A r 1 : ℤ) - sec A r 2) ^ 2
      + ((h : ℤ) - sec A r 1) * ((sec A r 2 : ℤ) - sec A r 0) ^ 2
      + ((h : ℤ) - sec A r 2) * ((sec A r 0 : ℤ) - sec A r 1) ^ 2) := by
  have hsum := sum_sec A r
  rw [sum_zmod3] at hsum
  have hs' : ((sec A r 0 : ℕ) : ℤ) + sec A r 1 + sec A r 2 = A.card := by exact_mod_cast hsum
  have hc2 : (c2 A r : ℤ) = (sec A r 0 : ℤ) ^ 2 + (sec A r 1 : ℤ) ^ 2 + (sec A r 2 : ℤ) ^ 2 := by
    rw [c2, sum_zmod3]; push_cast; ring
  have hc3 : (c3 A r : ℤ) = (sec A r 0 : ℤ) ^ 3 + (sec A r 1 : ℤ) ^ 3 + (sec A r 2 : ℤ) ^ 3 := by
    rw [c3, sum_zmod3]; push_cast; ring
  rw [E, hc2, hc3, ← hs']
  ring

theorem E_nonneg {A : Finset (Fin n → ZMod 3)} {h : ℕ} {r : Fin n → ZMod 3}
    (hh : ∀ t, sec A r t ≤ h) : 0 ≤ E A h r := by
  rw [E_eq]
  have h1 : (0 : ℤ) ≤ ((h : ℤ) - sec A r 0) * ((sec A r 1 : ℤ) - sec A r 2) ^ 2 :=
    mul_nonneg (by have := hh 0; omega) (sq_nonneg _)
  have h2 : (0 : ℤ) ≤ ((h : ℤ) - sec A r 1) * ((sec A r 2 : ℤ) - sec A r 0) ^ 2 :=
    mul_nonneg (by have := hh 1; omega) (sq_nonneg _)
  have h3 : (0 : ℤ) ≤ ((h : ℤ) - sec A r 2) * ((sec A r 0 : ℤ) - sec A r 1) ^ 2 :=
    mul_nonneg (by have := hh 2; omega) (sq_nonneg _)
  linarith

-- Summing the per-direction expression over all nonzero directions gives a closed form.
theorem be_sum {m : ℕ} {A : Finset (Fin (m + 2) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 2) → ZMod 3))) (h : ℕ) :
    ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), E A h r
      = 2 * (A.card : ℤ) * (9 * 3 ^ m * (1 + 3 * h) - A.card * (9 * 3 ^ m + 3 * h)) := by
  classical
  have hRcard : ((univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0)).card + 1
      = 9 * 3 ^ m := by
    have h1 : (univ : Finset (Fin (m + 2) → ZMod 3))
        = insert 0 (univ.filter (fun r => r ≠ 0)) := by
      ext r
      simp only [mem_univ, mem_insert, mem_filter, true_and, true_iff]
      tauto
    have h2 := congrArg Finset.card h1
    rw [card_insert_of_notMem (by simp), card_univ, card_fun] at h2
    have : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
    omega
  have hM2 := moment2 A
  have hM3 := moment3 hA
  have hexp : ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), E A h r
      = 9 * (∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), (c3 A r : ℤ))
        - 9 * (A.card : ℤ) * (∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), (c2 A r : ℤ))
        + ((univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0)).card * (2 * (A.card : ℤ) ^ 3)
        + (3 * (h : ℤ) - A.card) * (3 * (∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), (c2 A r : ℤ))
          - ((univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0)).card * (A.card : ℤ) ^ 2) := by
    simp only [E, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hM2' : (∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), (c2 A r : ℤ))
      + (A.card : ℤ) ^ 2 = 3 * 3 ^ m * (A.card : ℤ) ^ 2 + 6 * 3 ^ m * A.card := by
    exact_mod_cast hM2
  have hM3' : (∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), (c3 A r : ℤ))
      + (A.card : ℤ) ^ 3 = 3 ^ m * (A.card : ℤ) ^ 3 + 6 * 3 ^ m * (A.card : ℤ) ^ 2
        + 2 * 3 ^ m * A.card := by
    exact_mod_cast hM3
  have hR' : (((univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0)).card : ℤ) + 1
      = 9 * 3 ^ m := by exact_mod_cast hRcard
  rw [hexp]
  linear_combination 9 * hM3' + (9 * (h : ℤ) - 12 * A.card) * hM2'
    + (3 * (A.card : ℤ) ^ 3 - 3 * h * (A.card : ℤ) ^ 2) * hR'

-- The Bierbrauer–Edel / Davis–Maclagan bound: if every hyperplane section of a cap `A ⊆ F₃ⁿ`
-- has at most `h` points, then `|A| (3ⁿ + 3h) ≤ 3ⁿ (3h + 1)`.
theorem be_main {m : ℕ} {A : Finset (Fin (m + 2) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 2) → ZMod 3))) {h : ℕ}
    (hh : ∀ r : Fin (m + 2) → ZMod 3, r ≠ 0 → ∀ t, sec A r t ≤ h) :
    A.card * (3 ^ (m + 2) + 3 * h) ≤ 3 ^ (m + 2) * (3 * h + 1) := by
  classical
  have h9 : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
  have hsum : 0 ≤ ∑ r ∈ (univ : Finset (Fin (m + 2) → ZMod 3)).filter (fun r => r ≠ 0), E A h r :=
    Finset.sum_nonneg (fun r hr => E_nonneg (A := A) (h := h) (hh r (mem_filter.mp hr).2))
  rw [be_sum hA h] at hsum
  rcases Nat.eq_zero_or_pos A.card with hs0 | hspos
  · rw [hs0]; simp
  · have hpos : (0 : ℤ) < 2 * (A.card : ℤ) := by positivity
    have := (mul_nonneg_iff_of_pos_left hpos).mp hsum
    have hfin : (A.card : ℤ) * (9 * 3 ^ m + 3 * h) ≤ 9 * 3 ^ m * (3 * h + 1) := by linarith
    rw [h9]
    exact_mod_cast hfin

-- Dropping coordinate `i` is injective on the hyperplane `{x : r ⬝ᵥ x = t}` when `r i ≠ 0`.
theorem drop_inj {m : ℕ} {r : Fin (m + 1) → ZMod 3} {i : Fin (m + 1)} (hi : r i ≠ 0)
    {x y : Fin (m + 1) → ZMod 3} (hxy : r ⬝ᵥ x = r ⬝ᵥ y)
    (hp : ∀ j, x (i.succAbove j) = y (i.succAbove j)) : x = y := by
  have hdiff : ∀ j, j ≠ i → (x - y) j = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [hp k]
  have hdot : r ⬝ᵥ (x - y) = r i * (x - y) i := by
    rw [dotProduct, Finset.sum_eq_single i]
    · intro j _ hj; rw [hdiff j hj, mul_zero]
    · intro h; exact absurd (mem_univ i) h
  rw [dotProduct_sub, hxy, sub_self] at hdot
  have hi' : (x - y) i = 0 := by
    rcases mul_eq_zero.mp hdot.symm with h | h
    · exact absurd h hi
    · exact h
  funext j
  by_cases hj : j = i
  · subst hj; simpa [sub_eq_zero] using hi'
  · simpa [sub_eq_zero] using hdiff j hj

-- A hyperplane section of a cap in `F₃^(m+1)` is a cap in `F₃^m`, so has at most `f m` points.
theorem sec_le {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin (m + 1) → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin (m + 1) → ZMod 3))) {r : Fin (m + 1) → ZMod 3} (hr : r ≠ 0)
    (t : ZMod 3) : sec A r t ≤ SqueezeBench.CapSet.f m := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h; push Not at h; exact hr (funext h)
  let π : (Fin (m + 1) → ZMod 3) → (Fin m → ZMod 3) := fun x j => x (i.succAbove j)
  have hinj : Set.InjOn π (A.filter (fun x => r ⬝ᵥ x = t)) := by
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq] at hx hy
    exact drop_inj hi (by rw [hx.2, hy.2]) (fun j => congrFun hxy j)
  have hcap : ThreeAPFree (((A.filter (fun x => r ⬝ᵥ x = t)).image π : Finset (Fin m → ZMod 3))
      : Set (Fin m → ZMod 3)) := by
    intro a ha b hb c hc habc
    simp only [coe_image, Set.mem_image, mem_coe] at ha hb hc
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨z, hz, rfl⟩ := hc
    rw [mem_filter] at hx hy hz
    have hxz : x + z = y + y := by
      apply drop_inj hi
      · rw [dotProduct_add, dotProduct_add, hx.2, hz.2, hy.2]
      · intro j; exact congrFun habc j
    rw [hA (mem_coe.mpr hx.1) (mem_coe.mpr hy.1) (mem_coe.mpr hz.1) hxz]
  have h1 := SqueezeBench.CapSet.le_f_of_threeAPFree (n := m) hm hcap
  rw [card_image_of_injOn hinj] at h1
  exact h1


-- A set of nonzero vectors closed under negation has even size (`r ↦ -r` has no fixed point).
theorem even_card_of_neg {S : Finset (Fin n → ZMod 3)} (h0 : (0 : Fin n → ZMod 3) ∉ S)
    (hneg : ∀ r ∈ S, -r ∈ S) : Even S.card := by
  classical
  have hne : ∀ r ∈ S, r ≠ -r := by
    intro r hr h
    apply h0
    have : r = 0 := by
      funext i
      have := congrFun h i
      simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
      generalize r i = a at this ⊢; revert a; decide
    rw [this] at hr; exact hr
  rw [Finset.card_eq_sum_card_image (fun r => ({r, -r} : Finset (Fin n → ZMod 3))) S]
  have hfib : ∀ P ∈ S.image (fun r => ({r, -r} : Finset (Fin n → ZMod 3))),
      (S.filter (fun r => ({r, -r} : Finset (Fin n → ZMod 3)) = P)).card = 2 := by
    intro P hP
    rw [mem_image] at hP
    obtain ⟨r₀, hr₀, rfl⟩ := hP
    have : S.filter (fun r => ({r, -r} : Finset (Fin n → ZMod 3)) = {r₀, -r₀}) = {r₀, -r₀} := by
      ext r
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        have : r ∈ ({r₀, -r₀} : Finset (Fin n → ZMod 3)) := by
          rw [← h]; exact mem_insert_self _ _
        simpa using this
      · rintro (rfl | rfl)
        · exact ⟨hr₀, rfl⟩
        · exact ⟨hneg _ hr₀, by rw [neg_neg, Finset.pair_comm]⟩
    rw [this, Finset.card_pair (hne r₀ hr₀)]
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
  exact ⟨_, by ring⟩

theorem types21 (a b c : ℕ) (hs : a + b + c = 21) (ha : a ≤ 9) (hb : b ≤ 9) (hc : c ≤ 9)
    (h1 : a = 9 ∨ b = c) (h2 : b = 9 ∨ c = a) (h3 : c = 9 ∨ a = b) :
    a ^ 2 + b ^ 2 + c ^ 2 = 147 + if (a = 3 ∨ b = 3 ∨ c = 3) then 24 else 0 := by
  have : (a = 7 ∧ b = 7 ∧ c = 7) ∨ (a = 9 ∧ b = 9 ∧ c = 3) ∨ (a = 9 ∧ b = 3 ∧ c = 9)
      ∨ (a = 3 ∧ b = 9 ∧ c = 9) := by omega
  rcases this with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

theorem sec_neg (A : Finset (Fin n → ZMod 3)) (r : Fin n → ZMod 3) (t : ZMod 3) :
    sec A (-r) t = sec A r (-t) := by
  unfold sec
  congr 1
  ext x
  simp only [mem_filter, neg_dotProduct, neg_eq_iff_eq_neg]

-- The exact value `f 4 = 20`: a `21`-cap in `F₃⁴` would give equality in `be_main` with `h = 9`,
-- forcing every direction to have sections `(7,7,7)` or `(9,9,3)`; counting pairs then puts
-- `35` nonzero directions of the second kind, but they come in pairs `±r`.
theorem cap_four {A : Finset (Fin 4 → ZMod 3)} (hA : ThreeAPFree (A : Set (Fin 4 → ZMod 3))) :
    A.card ≤ 20 := by
  classical
  have h9 : ∀ r : Fin 4 → ZMod 3, r ≠ 0 → ∀ t, sec A r t ≤ 9 := by
    intro r hr t
    have h1 := sec_le (m := 3) (by norm_num) hA hr t
    have h3 := SqueezeBench.CapSet.Upper.V006.valid 3
    rw [show SqueezeBench.CapSet.Upper.V006.record 3 = 9 from by
      norm_num [SqueezeBench.CapSet.Upper.V006.record]] at h3
    omega
  have hmain := be_main (m := 2) hA h9
  by_contra h20
  have hs : A.card = 21 := by norm_num at hmain; omega
  have hsum := be_sum (m := 2) hA 9
  rw [hs] at hsum
  norm_num at hsum
  have hzero : ∀ r ∈ (univ : Finset (Fin 4 → ZMod 3)).filter (fun r => r ≠ 0), E A 9 r = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun r hr => E_nonneg (A := A) (h := 9) (h9 r (mem_filter.mp hr).2))).mp hsum
  have htype : ∀ r ∈ (univ : Finset (Fin 4 → ZMod 3)).filter (fun r => r ≠ 0),
      c2 A r = 147 + if (sec A r 0 = 3 ∨ sec A r 1 = 3 ∨ sec A r 2 = 3) then 24 else 0 := by
    intro r hr
    have hr0 := (mem_filter.mp hr).2
    have hE := hzero r hr
    rw [E_eq] at hE
    have t1 : (0 : ℤ) ≤ ((9 : ℕ) - sec A r 0 : ℤ) * ((sec A r 1 : ℤ) - sec A r 2) ^ 2 :=
      mul_nonneg (by have := h9 r hr0 0; omega) (sq_nonneg _)
    have t2 : (0 : ℤ) ≤ ((9 : ℕ) - sec A r 1 : ℤ) * ((sec A r 2 : ℤ) - sec A r 0) ^ 2 :=
      mul_nonneg (by have := h9 r hr0 1; omega) (sq_nonneg _)
    have t3 : (0 : ℤ) ≤ ((9 : ℕ) - sec A r 2 : ℤ) * ((sec A r 0 : ℤ) - sec A r 1) ^ 2 :=
      mul_nonneg (by have := h9 r hr0 2; omega) (sq_nonneg _)
    have e1 : ((9 : ℕ) - sec A r 0 : ℤ) * ((sec A r 1 : ℤ) - sec A r 2) ^ 2 = 0 := by linarith
    have e2 : ((9 : ℕ) - sec A r 1 : ℤ) * ((sec A r 2 : ℤ) - sec A r 0) ^ 2 = 0 := by linarith
    have e3 : ((9 : ℕ) - sec A r 2 : ℤ) * ((sec A r 0 : ℤ) - sec A r 1) ^ 2 = 0 := by linarith
    have hsum' := sum_sec A r
    rw [sum_zmod3, hs] at hsum'
    have d1 : sec A r 0 = 9 ∨ sec A r 1 = sec A r 2 := by
      rcases mul_eq_zero.mp e1 with h | h
      · left; omega
      · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; omega
    have d2 : sec A r 1 = 9 ∨ sec A r 2 = sec A r 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · left; omega
      · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; omega
    have d3 : sec A r 2 = 9 ∨ sec A r 0 = sec A r 1 := by
      rcases mul_eq_zero.mp e3 with h | h
      · left; omega
      · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; omega
    rw [c2, sum_zmod3]
    exact types21 _ _ _ hsum' (h9 r hr0 0) (h9 r hr0 1) (h9 r hr0 2) d1 d2 d3
  have hM2 := moment2 (m := 2) A
  rw [hs] at hM2
  norm_num at hM2
  rw [sum_congr rfl htype, sum_add_distrib, sum_const, smul_eq_mul, ← sum_filter, sum_const,
    smul_eq_mul] at hM2
  have hRcard : ((univ : Finset (Fin 4 → ZMod 3)).filter (fun r => r ≠ 0)).card = 80 := by
    have h1 : (univ : Finset (Fin 4 → ZMod 3)) = insert 0 (univ.filter (fun r => r ≠ 0)) := by
      ext r
      simp only [mem_univ, mem_insert, mem_filter, true_and, true_iff]
      tauto
    have h2 := congrArg Finset.card h1
    rw [card_insert_of_notMem (by simp), card_univ, card_fun] at h2
    omega
  rw [hRcard] at hM2
  have heven := even_card_of_neg
    (S := ((univ : Finset (Fin 4 → ZMod 3)).filter (fun r => r ≠ 0)).filter
      (fun r => sec A r 0 = 3 ∨ sec A r 1 = 3 ∨ sec A r 2 = 3))
    (by simp) (by
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      refine ⟨neg_ne_zero.mpr hr.1, ?_⟩
      rw [sec_neg, sec_neg, sec_neg]
      have e1 : (-(1 : ZMod 3)) = 2 := by decide
      have e2 : (-(2 : ZMod 3)) = 1 := by decide
      rw [neg_zero, e1, e2]
      tauto)
  obtain ⟨k, hk⟩ := heven
  omega


-- One step of the recursion: from `f m ≤ h` to `f (m+1) ≤ step (3^m) h`, for `m ≥ 3`.
theorem step_valid {m : ℕ} (hm : 3 ≤ m) {h : ℕ} (hh : SqueezeBench.CapSet.f m ≤ h) :
    SqueezeBench.CapSet.f (m + 1) ≤ step (3 ^ m) h := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hnm : SqueezeBench.CapSet.nMin ≤ k + 3 + 1 := by simp [SqueezeBench.CapSet.nMin]
  have hlt : SqueezeBench.CapSet.f (k + 3 + 1) < step (3 ^ (k + 3)) h + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have hsec : ∀ r : Fin (k + 3 + 1) → ZMod 3, r ≠ 0 → ∀ t, sec A r t ≤ h := by
      intro r hr t
      exact (sec_le (m := k + 3) (by omega) hAPF hr t).trans hh
    have hmain := be_main (m := k + 2) hAPF hsec
    have h3 : 3 ^ (k + 2 + 2) = 3 * 3 ^ (k + 3) := by ring
    rw [h3] at hmain
    have h4 : A.card * (3 ^ (k + 3) + h) ≤ 3 ^ (k + 3) * (3 * h + 1) := by
      have h4' : 3 * (A.card * (3 ^ (k + 3) + h)) ≤ 3 * (3 ^ (k + 3) * (3 * h + 1)) := by
        calc 3 * (A.card * (3 ^ (k + 3) + h)) = A.card * (3 * 3 ^ (k + 3) + 3 * h) := by ring
          _ ≤ 3 * 3 ^ (k + 3) * (3 * h + 1) := hmain
          _ = 3 * (3 ^ (k + 3) * (3 * h + 1)) := by ring
      exact Nat.le_of_mul_le_mul_left h4' (by norm_num)
    have h5 : A.card ≤ step (3 ^ (k + 3)) h := by
      unfold step
      rw [Nat.le_div_iff_mul_le (by positivity)]
      exact h4
    omega
  omega

theorem chain_valid : ∀ k, SqueezeBench.CapSet.f (k + 4) ≤ chain k := by
  intro k
  induction k with
  | zero =>
    have hnm : SqueezeBench.CapSet.nMin ≤ 4 := by simp [SqueezeBench.CapSet.nMin]
    have hlt : SqueezeBench.CapSet.f 4 < 21 := by
      refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
      intro A hA hAPF
      simp only [mem_powersetCard_univ] at hA
      have := cap_four hAPF
      omega
    rw [chain]
    show SqueezeBench.CapSet.f 4 ≤ 20
    omega
  | succ k ih =>
    rw [chain]
    exact step_valid (m := k + 4) (by omega) ih

theorem hyperBound_valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f hyperBound := by
  intro n
  unfold hyperBound
  rcases Nat.lt_or_ge n 4 with h | h
  · rw [show n - 4 = 0 from by omega, chain]
    have h6 := SqueezeBench.CapSet.Upper.V006.valid n
    have : SqueezeBench.CapSet.Upper.V006.record n ≤ 20 := by
      interval_cases n <;> norm_num [SqueezeBench.CapSet.Upper.V006.record]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 4 = k from by omega]
    exact chain_valid k

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record :=
  SqueezeBench.minWith_valid SqueezeBench.CapSet.Upper.V007.valid hyperBound_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V007.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V007.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.CapSet.nMin) (n₀ := 4) (by decide)
    (by decide +kernel)

end SqueezeBench.CapSet.Upper.V008
