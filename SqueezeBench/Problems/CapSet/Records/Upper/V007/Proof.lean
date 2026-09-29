import SqueezeBench.Problems.CapSet.Records.Upper.V007.Def
import SqueezeBench.Problems.CapSet.Records.Upper.V006.Proof

/-! Record V007 for CapSet, upper direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Upper/V007.lean`.

The Ellenberg–Gijswijt bound, in the linear-algebra form of the original paper: for a cap
`A ⊆ F₃ⁿ` and any `d`, `|A| ≤ 3ⁿ - m_d + 2 m_{⌊d/2⌋}`, where `m_d` is the number of monomials
`x₁^{a₁} ⋯ xₙ^{aₙ}` with `aᵢ ≤ 2` and `∑ aᵢ ≤ d`. Polynomials are handled as functions
`F₃ⁿ → F₃` spanned by the reduced monomials. The record reads `m_d` off the base-`B` digits of
`(1 + B + B²)ⁿ`, `B = 3ⁿ + 1` (`genfun`, `digit_sum`), so that the kernel evaluates it with a
few big-number operations. -/

namespace SqueezeBench.CapSet.Upper.V007

open SqueezeBench Finset

variable {n : ℕ}


-- Reduced monomial `x ↦ ∏ i, x i ^ a i`, exponent vector `a ∈ {0,1,2}ⁿ`.
def mono (a : Fin n → Fin 3) : (Fin n → ZMod 3) → ZMod 3 := fun x => ∏ i, x i ^ (a i : ℕ)

-- Total degree of an exponent vector.
def deg (a : Fin n → Fin 3) : ℕ := ∑ i, (a i : ℕ)

-- One-variable indicator of `t ∈ ZMod 3` is a quadratic polynomial.
theorem delta_eq (t s : ZMod 3) :
    (if s = t then (1 : ZMod 3) else 0) = ∑ k : Fin 3, (![1 - t ^ 2, 2 * t, -1] k) * s ^ (k : ℕ) := by
  revert t s; decide

-- The point indicator `δ_c` is a linear combination of monomials.
theorem indicator_mem_span (c : Fin n → ZMod 3) :
    (fun x : Fin n → ZMod 3 => if x = c then (1 : ZMod 3) else 0)
      ∈ Submodule.span (ZMod 3) (Set.range (mono (n := n))) := by
  classical
  have hfun : (fun x : Fin n → ZMod 3 => if x = c then (1 : ZMod 3) else 0)
      = ∑ a : Fin n → Fin 3, (∏ i, (![1 - c i ^ 2, 2 * c i, -1] (a i))) • mono a := by
    funext x
    have h1 : (if x = c then (1 : ZMod 3) else 0) = ∏ i, (if x i = c i then (1 : ZMod 3) else 0) := by
      by_cases h : x = c
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ c i := by
          by_contra hcon
          push Not at hcon
          exact h (funext hcon)
        rw [eq_comm]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])
    rw [h1]
    simp_rw [delta_eq (c _) (x _)]
    rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 3))) (fun i k => (![1 - c i ^ 2, 2 * c i, -1] k) * x i ^ (k : ℕ))]
    rw [Fintype.piFinset_univ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mono, Finset.prod_mul_distrib]
  rw [hfun]
  refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem top_le_span_mono : ⊤ ≤ Submodule.span (ZMod 3) (Set.range (mono (n := n))) := by
  classical
  rw [← (Pi.basisFun (ZMod 3) (Fin n → ZMod 3)).span_eq, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  rw [Pi.basisFun_apply]
  have : (Pi.single c (1 : ZMod 3) : (Fin n → ZMod 3) → ZMod 3)
      = fun x => if x = c then (1 : ZMod 3) else 0 := by
    funext x
    by_cases h : x = c
    · subst h; simp
    · rw [if_neg h, Pi.single_apply, if_neg h]
  rw [this]
  exact indicator_mem_span c

theorem linearIndependent_mono : LinearIndependent (ZMod 3) (mono (n := n)) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank top_le_span_mono ?_
  rw [Module.finrank_fintype_fun_eq_card]
  simp


-- The exponent vectors of degree at most `d`.
def expo (n d : ℕ) : Finset (Fin n → Fin 3) := univ.filter (fun a => deg a ≤ d)

-- The polynomial functions of degree at most `d`.
def polySpace (n d : ℕ) : Submodule (ZMod 3) ((Fin n → ZMod 3) → ZMod 3) :=
  Submodule.span (ZMod 3) (Set.range (mono ∘ (Subtype.val : expo n d → Fin n → Fin 3)))

theorem finrank_polySpace (n d : ℕ) :
    Module.finrank (ZMod 3) (polySpace n d) = (expo n d).card := by
  classical
  rw [polySpace, finrank_span_eq_card (linearIndependent_mono.comp Subtype.val Subtype.val_injective)]
  exact Fintype.card_coe _

-- Functions vanishing on a finite set `S`.
def vanish (S : Finset (Fin n → ZMod 3)) : Submodule (ZMod 3) ((Fin n → ZMod 3) → ZMod 3) :=
  LinearMap.ker (LinearMap.funLeft (ZMod 3) (ZMod 3) (Subtype.val : S → Fin n → ZMod 3))

theorem mem_vanish {S : Finset (Fin n → ZMod 3)} {P : (Fin n → ZMod 3) → ZMod 3} :
    P ∈ vanish S ↔ ∀ x ∈ S, P x = 0 := by
  simp only [vanish, LinearMap.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [LinearMap.funLeft_apply] using this
  · intro h
    funext ⟨x, hx⟩
    simp [LinearMap.funLeft_apply, h x hx]

theorem card_fun : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by simp

-- Rank–nullity for the restriction map: vanishing on `S` costs at most `|S|` dimensions.
theorem finrank_vanish_ge (S : Finset (Fin n → ZMod 3)) :
    3 ^ n ≤ Module.finrank (ZMod 3) (vanish S) + S.card := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft (ZMod 3) (ZMod 3) (Subtype.val : S → Fin n → ZMod 3))
  have h2 := Submodule.finrank_le
    (LinearMap.range (LinearMap.funLeft (ZMod 3) (ZMod 3) (Subtype.val : S → Fin n → ZMod 3)))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  rw [Module.finrank_fintype_fun_eq_card, card_fun] at h
  unfold vanish
  omega

theorem finrank_inf_vanish (W : Submodule (ZMod 3) ((Fin n → ZMod 3) → ZMod 3))
    (S : Finset (Fin n → ZMod 3)) :
    Module.finrank (ZMod 3) W ≤ Module.finrank (ZMod 3) ↥(W ⊓ vanish S) + S.card := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (vanish S)
  have h2 := Submodule.finrank_le (W ⊔ vanish S)
  rw [Module.finrank_fintype_fun_eq_card, card_fun] at h2
  have h3 := finrank_vanish_ge S
  omega

-- The support of a function.
def supp (P : (Fin n → ZMod 3) → ZMod 3) : Finset (Fin n → ZMod 3) := univ.filter (fun x => P x ≠ 0)

theorem mem_supp {P : (Fin n → ZMod 3) → ZMod 3} {x : Fin n → ZMod 3} : x ∈ supp P ↔ P x ≠ 0 := by
  simp [supp]

-- A subspace of functions contains an element whose support is at least its dimension:
-- restriction to the support of a maximal-support element is injective.
theorem exists_large_supp (W : Submodule (ZMod 3) ((Fin n → ZMod 3) → ZMod 3)) :
    ∃ P ∈ W, Module.finrank (ZMod 3) W ≤ (supp P).card := by
  classical
  obtain ⟨P, hPW, hmax⟩ := Finset.exists_max_image
    ((univ : Finset ((Fin n → ZMod 3) → ZMod 3)).filter (· ∈ W)) (fun Q => (supp Q).card)
    ⟨0, by simp⟩
  rw [mem_filter] at hPW
  refine ⟨P, hPW.2, ?_⟩
  let ρ : W →ₗ[ZMod 3] (supp P → ZMod 3) :=
    (LinearMap.funLeft (ZMod 3) (ZMod 3) (Subtype.val : supp P → Fin n → ZMod 3)).comp W.subtype
  have hinj : Function.Injective ρ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Q hQ
    by_contra hne
    have hvan : ∀ x ∈ supp P, Q.1 x = 0 := by
      intro x hx
      have := congrFun hQ ⟨x, hx⟩
      simpa [ρ, LinearMap.funLeft_apply] using this
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, Q.1 x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Subtype.ext (funext hcon))
    have hx₀P : P x₀ = 0 := by
      by_contra h
      exact hx₀ (hvan x₀ (mem_supp.mpr h))
    have hsub : insert x₀ (supp P) ⊆ supp (P + Q.1) := by
      intro x hx
      rw [mem_insert] at hx
      rw [mem_supp, Pi.add_apply]
      rcases hx with rfl | hx
      · rw [hx₀P, zero_add]; exact hx₀
      · rw [hvan x hx, add_zero]; exact mem_supp.mp hx
    have hnotin : x₀ ∉ supp P := by rw [mem_supp]; exact not_not.mpr hx₀P
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hnotin] at hcard
    have := hmax (P + Q.1) (by rw [mem_filter]; exact ⟨mem_univ _, W.add_mem hPW.2 Q.2⟩)
    omega
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this

-- Two-variable functions of the form `Σ_b mono b x * g b y + Σ_c h c x * mono c y`, with
-- `b, c` of degree at most `D`.
def Good (D : ℕ) (F : (Fin n → ZMod 3) → (Fin n → ZMod 3) → ZMod 3) : Prop :=
  ∃ g h : (Fin n → Fin 3) → (Fin n → ZMod 3) → ZMod 3,
    ∀ x y, F x y = ∑ b ∈ expo n D, mono b x * g b y + ∑ c ∈ expo n D, h c x * mono c y

theorem good_zero (D : ℕ) : Good (n := n) D 0 := ⟨0, 0, fun x y => by simp⟩

theorem good_add {D : ℕ} {F G : (Fin n → ZMod 3) → (Fin n → ZMod 3) → ZMod 3}
    (hF : Good D F) (hG : Good D G) : Good D (F + G) := by
  obtain ⟨g₁, h₁, e₁⟩ := hF
  obtain ⟨g₂, h₂, e₂⟩ := hG
  refine ⟨g₁ + g₂, h₁ + h₂, fun x y => ?_⟩
  simp only [Pi.add_apply, e₁, e₂, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem good_smul {D : ℕ} {F : (Fin n → ZMod 3) → (Fin n → ZMod 3) → ZMod 3} (c : ZMod 3)
    (hF : Good D F) : Good D (c • F) := by
  obtain ⟨g, h, e⟩ := hF
  refine ⟨c • g, c • h, fun x y => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, e, Finset.mul_sum, mul_add]
  congr 1 <;> refine Finset.sum_congr rfl (fun _ _ => by ring)

theorem good_prod {D : ℕ} (b c : Fin n → Fin 3) (hbc : deg b ≤ D ∨ deg c ≤ D) :
    Good D (fun x y => mono b x * mono c y) := by
  classical
  rcases hbc with hb | hc
  · refine ⟨fun b' => if b' = b then mono c else 0, 0, fun x y => ?_⟩
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, ite_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', expo, mem_filter, mem_univ, true_and, hb, if_true]
  · refine ⟨0, fun c' => if c' = c then mono b else 0, fun x y => ?_⟩
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, ite_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq', expo, mem_filter, mem_univ, true_and, hc, if_true]

-- A `Good` function, evaluated on a finite family of points, has rank at most `2 m_D`.
theorem rank_le_of_good {D : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin n → ZMod 3)) {F : (Fin n → ZMod 3) → (Fin n → ZMod 3) → ZMod 3}
    (hF : Good D F) :
    (Matrix.of (fun i j : ι => F (v i) (v j))).rank ≤ 2 * (expo n D).card := by
  classical
  obtain ⟨g, h, e⟩ := hF
  let U : Matrix ι (expo n D ⊕ expo n D) (ZMod 3) :=
    Matrix.of (fun i bc => Sum.elim (fun b : expo n D => mono b.1 (v i)) (fun c : expo n D => h c.1 (v i)) bc)
  let Vm : Matrix (expo n D ⊕ expo n D) ι (ZMod 3) :=
    Matrix.of (fun bc j => Sum.elim (fun b : expo n D => g b.1 (v j)) (fun c : expo n D => mono c.1 (v j)) bc)
  have hUV : Matrix.of (fun i j : ι => F (v i) (v j)) = U * Vm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, U, Vm, Sum.elim_inl,
      Sum.elim_inr, e]
    rw [Finset.sum_coe_sort (expo n D) (fun b => mono b (v i) * g b (v j)),
      Finset.sum_coe_sort (expo n D) (fun c => h c (v i) * mono c (v j))]
  rw [hUV]
  calc (U * Vm).rank ≤ U.rank := Matrix.rank_mul_le_left U Vm
    _ ≤ Fintype.card (expo n D ⊕ expo n D) := Matrix.rank_le_card_width U
    _ = 2 * (expo n D).card := by rw [Fintype.card_sum, Fintype.card_coe]; ring


-- Truncated difference of exponent vectors.
def esub (a k : Fin n → Fin 3) : Fin n → Fin 3 :=
  fun i => ⟨(a i : ℕ) - (k i : ℕ), lt_of_le_of_lt (Nat.sub_le _ _) (a i).isLt⟩

-- The coefficient of `x^k y^(a-k)` in `(-(x+y))^a`, coordinatewise.
def coef (a k : Fin n → Fin 3) : ZMod 3 :=
  ∏ i, ((Nat.choose (a i) (k i) : ZMod 3) * (-1) ^ (a i : ℕ))

theorem one_var (t : Fin 3) (s u : ZMod 3) :
    (-(s + u)) ^ (t : ℕ) = ∑ k : Fin 3, ((Nat.choose t k : ZMod 3) * (-1) ^ (t : ℕ))
      * (s ^ (k : ℕ) * u ^ ((t : ℕ) - k)) := by
  fin_cases t <;> simp [Fin.sum_univ_three] <;> ring

theorem mono_neg_add (a : Fin n → Fin 3) (x y : Fin n → ZMod 3) :
    mono a (-(x + y)) = ∑ k : Fin n → Fin 3, coef a k * (mono k x * mono (esub a k) y) := by
  classical
  unfold mono coef
  simp only [Pi.neg_apply, Pi.add_apply]
  simp_rw [one_var]
  rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 3)))
    (fun i k => ((Nat.choose (a i) k : ZMod 3) * (-1) ^ (a i : ℕ))
      * (x i ^ (k : ℕ) * y i ^ ((a i : ℕ) - k)))]
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Finset.prod_mul_distrib]
  rfl

theorem deg_add_esub {a k : Fin n → Fin 3} (hk : ∀ i, (k i : ℕ) ≤ a i) :
    deg k + deg (esub a k) = deg a := by
  unfold deg esub
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  change (k i : ℕ) + ((a i : ℕ) - (k i : ℕ)) = (a i : ℕ)
  have := hk i; omega

theorem coef_eq_zero {a k : Fin n → Fin 3} (hk : ¬ ∀ i, (k i : ℕ) ≤ a i) : coef a k = 0 := by
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  unfold coef
  apply Finset.prod_eq_zero (mem_univ i)
  rw [Nat.choose_eq_zero_of_lt hi]; simp

theorem good_mono_neg_add {d : ℕ} (a : Fin n → Fin 3) (ha : deg a ≤ d) :
    Good (d / 2) (fun x y => mono a (-(x + y))) := by
  classical
  have : (fun x y => mono a (-(x + y)))
      = ∑ k : Fin n → Fin 3, coef a k • (fun x y => mono k x * mono (esub a k) y) := by
    funext x y
    rw [mono_neg_add]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  refine Finset.sum_induction _ (Good (d / 2)) (fun _ _ => good_add) (good_zero _) (fun k _ => ?_)
  by_cases hk : ∀ i, (k i : ℕ) ≤ a i
  · refine good_smul _ (good_prod _ _ ?_)
    have := deg_add_esub hk
    omega
  · rw [coef_eq_zero hk, zero_smul]
    exact good_zero _

theorem good_of_mem_polySpace {d : ℕ} {P : (Fin n → ZMod 3) → ZMod 3} (hP : P ∈ polySpace n d) :
    Good (d / 2) (fun x y => P (-(x + y))) := by
  classical
  unfold polySpace at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨a, rfl⟩ := hP
    exact good_mono_neg_add a.1 (Finset.mem_filter.mp a.2).2
  | zero => exact good_zero _
  | add P Q _ _ hP hQ => exact good_add hP hQ
  | smul c P _ hP => exact good_smul c hP

theorem neg_add_self' (v : ZMod 3) : -(v + v) = v := by revert v; decide
theorem line_eq (u v : ZMod 3) : u + -(u + v) = v + v := by revert u v; decide

-- The Ellenberg–Gijswijt bound: for every `d`, `|A| + m_d ≤ 3^n + 2 m_{d/2}`.
theorem eg_bound {A : Finset (Fin n → ZMod 3)} (hA : ThreeAPFree (A : Set (Fin n → ZMod 3)))
    (d : ℕ) : A.card + (expo n d).card ≤ 3 ^ n + 2 * (expo n (d / 2)).card := by
  classical
  have hW := finrank_inf_vanish (polySpace n d) (univ \ A)
  rw [finrank_polySpace, card_univ_sdiff, card_fun] at hW
  obtain ⟨P, hPW, hsupp⟩ := exists_large_supp (polySpace n d ⊓ vanish (univ \ A))
  rw [Submodule.mem_inf, mem_vanish] at hPW
  obtain ⟨hPd, hPvan⟩ := hPW
  have hsuppA : ∀ x ∈ supp P, x ∈ A := by
    intro x hx
    by_contra h
    exact (mem_supp.mp hx) (hPvan x (by rw [mem_sdiff]; exact ⟨mem_univ _, h⟩))
  have hgood := good_of_mem_polySpace hPd
  have hrank := rank_le_of_good (Subtype.val : supp P → Fin n → ZMod 3) hgood
  have hdiag : Matrix.of (fun x y : supp P => P (-(x.1 + y.1)))
      = Matrix.diagonal (fun x : supp P => P x.1) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [Matrix.of_apply, Matrix.diagonal_apply_eq]
      congr 1
      funext i
      exact neg_add_self' (x.1 i)
    · rw [Matrix.of_apply, Matrix.diagonal_apply_ne _ hxy]
      apply hPvan
      rw [mem_sdiff]
      refine ⟨mem_univ _, fun hz => hxy ?_⟩
      apply Subtype.ext
      exact hA (mem_coe.mpr (hsuppA _ x.2)) (mem_coe.mpr (hsuppA _ y.2)) (mem_coe.mpr hz)
        (funext fun i => line_eq (x.1 i) (y.1 i))
  rw [hdiag, Matrix.rank_diagonal] at hrank
  have hall : ∀ x : supp P, P x.1 ≠ 0 := fun x => mem_supp.mp x.2
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_coe] at hrank
  have hA3 : A.card ≤ 3 ^ n := by
    have := card_le_univ A; rwa [card_fun] at this
  omega





-- Number of exponent vectors of degree exactly `k`.
def cnt (n k : ℕ) : ℕ := (univ.filter (fun a : Fin n → Fin 3 => deg a = k)).card

theorem card_expo (n d : ℕ) : (expo n d).card = ∑ k ∈ range (d + 1), cnt n k := by
  classical
  unfold expo cnt
  rw [card_eq_sum_card_fiberwise (f := deg) (t := range (d + 1))]
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_range] at hk ⊢
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  · intro a ha
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha
    simp only [coe_range, Set.mem_Iio]
    omega

-- Σ_{i < k} c i * B^i < B^k when every c i < B.
theorem sum_lt_pow {B : ℕ} (c : ℕ → ℕ) (hc : ∀ i, c i < B) (k : ℕ) :
    ∑ i ∈ range k, c i * B ^ i < B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    have h1 : (c k + 1) * B ^ k ≤ B * B ^ k := Nat.mul_le_mul_right _ (hc k)
    rw [add_mul, one_mul, mul_comm B] at h1
    omega

-- Digit `k` of `Σ_{i ≤ N} c i * B^i` is `c k` (for `k ≤ N`) when every `c i < B`.
theorem digit_sum {B : ℕ} (hB : 2 ≤ B) (c : ℕ → ℕ) (hc : ∀ i, c i < B) (N k : ℕ) (hk : k ≤ N) :
    (∑ i ∈ range (N + 1), c i * B ^ i) / B ^ k % B = c k := by
  have hBpos : 0 < B ^ k := Nat.pow_pos (by omega)
  -- split the sum: i < k, i = k, i > k
  have hsplit : ∑ i ∈ range (N + 1), c i * B ^ i
      = ∑ i ∈ range k, c i * B ^ i + B ^ k * (c k + B * ∑ j ∈ range (N - k), c (k + 1 + j) * B ^ j) := by
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ N + 1),
      ← range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : k < N + 1),
      Finset.sum_Ico_eq_sum_range]
    rw [show N + 1 - (k + 1) = N - k from by omega]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show k + 1 + j = j + (k + 1) from by ring, pow_add, pow_succ]
      ring
  rw [hsplit, Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt (sum_lt_pow c hc k),
    zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc k)]

-- Beyond the top index the digits vanish.
theorem digit_sum_high {B : ℕ} (hB : 2 ≤ B) (c : ℕ → ℕ) (hc : ∀ i, c i < B) (N k : ℕ)
    (hk : N < k) : (∑ i ∈ range (N + 1), c i * B ^ i) / B ^ k % B = 0 := by
  have h := sum_lt_pow c hc (N + 1)
  have h2 : B ^ (N + 1) ≤ B ^ k := Nat.pow_le_pow_right (by omega) hk
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_mod]

theorem deg_le (a : Fin n → Fin 3) : deg a ≤ 2 * n := by
  unfold deg
  calc ∑ i, (a i : ℕ) ≤ ∑ _i : Fin n, 2 :=
        Finset.sum_le_sum (fun i _ => Nat.lt_succ_iff.mp (a i).isLt)
    _ = 2 * n := by simp [mul_comm]

-- The generating function: `(1 + B + B²)^n = Σ_k cnt n k * B^k`.
theorem genfun (n B : ℕ) : (1 + B + B ^ 2) ^ n = ∑ k ∈ range (2 * n + 1), cnt n k * B ^ k := by
  classical
  have h1 : (1 + B + B ^ 2) ^ n = ∏ _i : Fin n, ∑ t : Fin 3, B ^ (t : ℕ) := by
    rw [Finset.prod_const, card_univ, Fintype.card_fin, Fin.sum_univ_three]
    simp
  rw [h1, Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 3))) (fun _ t => B ^ (t : ℕ)),
    Fintype.piFinset_univ]
  simp_rw [Finset.prod_pow_eq_pow_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun a : Fin n → Fin 3 => deg a) (t := range (2 * n + 1))
    (fun a _ => mem_range.mpr (Nat.lt_succ_of_le (deg_le a)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold cnt
  rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [mem_filter] at ha
  show B ^ deg a = B ^ k
  rw [ha.2]


-- `deg a ≤ 2n`, so the count of degree `k > 2n` is `0`.
theorem cnt_eq_zero {n k : ℕ} (hk : 2 * n < k) : cnt n k = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _
  have := deg_le a
  omega

theorem cnt_lt (n k : ℕ) : cnt n k < 3 ^ n + 1 := by
  unfold cnt
  have := card_le_univ (univ.filter (fun a : Fin n → Fin 3 => deg a = k))
  simp only [Fintype.card_fun, Fintype.card_fin] at this
  omega

-- The digits of `(1 + B + B²)ⁿ` in base `B = 3ⁿ + 1` are the counts.
theorem digit_eq (n k : ℕ) :
    digit ((1 + (3 ^ n + 1) + (3 ^ n + 1) ^ 2) ^ n) (3 ^ n + 1) k = cnt n k := by
  unfold digit
  rw [genfun n (3 ^ n + 1)]
  have hB : 2 ≤ 3 ^ n + 1 := by have := Nat.one_le_pow n 3 (by norm_num); omega
  rcases Nat.lt_or_ge (2 * n) k with hk | hk
  · rw [digit_sum_high hB _ (cnt_lt n) (2 * n) k hk, cnt_eq_zero hk]
  · exact digit_sum hB _ (cnt_lt n) (2 * n) k hk

theorem msum_eq (n d : ℕ) :
    msum ((1 + (3 ^ n + 1) + (3 ^ n + 1) ^ 2) ^ n) (3 ^ n + 1) d = (expo n d).card := by
  rw [card_expo]
  induction d with
  | zero => simp [msum, digit_eq]
  | succ d ih => rw [msum, ih, digit_eq, Finset.sum_range_succ (fun k => cnt n k) (d + 1)]

theorem card_expo_le (n d : ℕ) : (expo n d).card ≤ 3 ^ n := by
  calc (expo n d).card ≤ (univ : Finset (Fin n → Fin 3)).card := card_le_univ _
    _ = 3 ^ n := by simp

-- Every `d` gives an upper bound on `f n`.
theorem f_le_eg (n : ℕ) (hn : 1 ≤ n) (d : ℕ) : SqueezeBench.CapSet.f n
    ≤ eg n ((1 + (3 ^ n + 1) + (3 ^ n + 1) ^ 2) ^ n) (3 ^ n + 1) d := by
  have hnm : SqueezeBench.CapSet.nMin ≤ n := hn
  have hlt : SqueezeBench.CapSet.f n
      < eg n ((1 + (3 ^ n + 1) + (3 ^ n + 1) ^ 2) ^ n) (3 ^ n + 1) d + 1 := by
    refine SqueezeBench.CapSet.f_lt_of_forall_not hnm ?_
    intro A hA hAPF
    simp only [mem_powersetCard_univ] at hA
    have hb := eg_bound hAPF d
    have hm := card_expo_le n d
    unfold eg at hA
    rw [msum_eq, msum_eq] at hA
    omega
  omega

theorem f_le_egWin (n : ℕ) (hn : 1 ≤ n) (D : ℕ) : SqueezeBench.CapSet.f n
    ≤ egWin n ((1 + (3 ^ n + 1) + (3 ^ n + 1) ^ 2) ^ n) (3 ^ n + 1) D := by
  unfold egWin
  exact le_min (le_min (f_le_eg n hn _) (f_le_eg n hn _))
    (le_min (f_le_eg n hn _) (le_min (f_le_eg n hn _) (f_le_eg n hn _)))

theorem egBound_valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f egBound := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [SqueezeBench.CapSet.f, SqueezeBench.CapSet.nMin]
  · exact f_le_egWin n hn _

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.CapSet.f record :=
  SqueezeBench.minWith_valid SqueezeBench.CapSet.Upper.V006.valid egBound_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.CapSet.Upper.V006.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.CapSet.nMin
      SqueezeBench.CapSet.Upper.V006.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.CapSet.nMin) (n₀ := 9) (by decide)
    (by decide +kernel)

end SqueezeBench.CapSet.Upper.V007
