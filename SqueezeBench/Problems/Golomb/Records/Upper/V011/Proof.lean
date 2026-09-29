import SqueezeBench.Problems.Golomb.Records.Upper.V011.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V010.Proof

-- Golomb upper-bound record V011 — validity.
-- V010's Singer argument, restated over an arbitrary finite field `K` with `q` elements and a
-- ring homomorphism `ι : K →+* L` into a field `L` with `q³` elements: the only facts about the
-- prime field it used were `|K| = q`, `x^(q-1) = 1` for `x ≠ 0` (`pow_card_sub_one`, from
-- Lagrange in `Kˣ`) and the injectivity of `ι`. The lemmas `mem_base_of_pow_eq_one`,
-- `gen_not_base`, `exp_eq_of_proportional`, `lin_indep3`, `proportional` and the main theorem
-- `f_le_singer_general` are V010's with `ZMod p` replaced by `K`, `GaloisField p 3` by `L`.
-- `f_le_singer_pp` instantiates `K = GaloisField p k`, `L = GaloisField p (3k)` for `q = p^k`,
-- with `ι` from `FiniteField.nonempty_algHom_of_finrank_dvd` (`k ∣ 3k`) and the cardinalities
-- from `GaloisField.card`. `primePowGe_spec` is V009's `primeGe_spec` with `IsPrimePow`, since
-- Bertrand's prime is in particular a prime power.

namespace SqueezeBench.Golomb.Upper.V011

open SqueezeBench Finset
open SqueezeBench.Golomb.Upper.V008 (SidonMod f_le_of_sidonMod)

section SingerGeneral

variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L]

theorem cube_sub_one' {q : ℕ} (hq : 2 ≤ q) : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h : (r + 1) ^ 3 = ((r + 1) ^ 2 + (r + 1) + 1) * r + 1 := by ring
  simp only [Nat.add_sub_cancel]
  omega

omit [Finite K] in
/-- Nonzero elements of a field with `q` elements satisfy `x^(q-1) = 1`. -/
theorem pow_card_sub_one {q : ℕ} (hK : Nat.card K = q) {x : K} (hx : x ≠ 0) :
    x ^ (q - 1) = 1 := by
  have h := pow_card_eq_one' (x := Units.mk0 x hx)
  rw [Nat.card_units, hK] at h
  have := congrArg Units.val h
  simpa using this

/-- Units of `L` with `x^(q-1) = 1` lie in the image of `K`: a cyclic group has at most
`q - 1` such elements, and `K` already supplies `q - 1`. -/
theorem mem_base_of_pow_eq_one {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q) (ι : K →+* L)
    {x : Lˣ} (h : x ^ (q - 1) = 1) : ∃ c : K, (x : L) = ι c := by
  classical
  haveI : Fintype Lˣ := Fintype.ofFinite _
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have hT := IsCyclic.card_pow_eq_one_le (α := Lˣ) (n := q - 1) (by omega)
  let φ : Kˣ →* Lˣ := Units.map ι.toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective ι.injective
  have hsub : (univ : Finset Kˣ).image φ ⊆ univ.filter (fun a => a ^ (q - 1) = 1) := by
    intro a ha
    rw [mem_image] at ha
    obtain ⟨c, _, rfl⟩ := ha
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hc : c ^ (q - 1) = 1 := by rw [← hK, ← Nat.card_units]; exact pow_card_eq_one'
    rw [← map_pow, hc, map_one]
  have hcard : (univ.filter (fun a : Lˣ => a ^ (q - 1) = 1)).card
      ≤ ((univ : Finset Kˣ).image φ).card := by
    rw [card_image_of_injective _ hφ, card_univ, Fintype.card_eq_nat_card, Nat.card_units, hK]
    exact hT
  have heq := eq_of_subset_of_card_le hsub hcard
  have hx : x ∈ univ.filter (fun a : Lˣ => a ^ (q - 1) = 1) := by
    rw [mem_filter]; exact ⟨mem_univ _, h⟩
  rw [← heq, mem_image] at hx
  obtain ⟨c, _, rfl⟩ := hx
  exact ⟨c, rfl⟩

omit [Finite L] in
/-- A generator of `Lˣ` lies outside the image of `K`. -/
theorem gen_not_base {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q) (ι : K →+* L) {θ : Lˣ}
    (hθ : orderOf θ = q ^ 3 - 1) (c : K) : (θ : L) ≠ ι c := by
  intro h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact θ.ne_zero h
  have h1 : (θ : L) ^ (q - 1) = 1 := by
    rw [h, ← map_pow, pow_card_sub_one hK hc, map_one]
  have h2 : θ ^ (q - 1) = 1 := Units.ext (by simpa using h1)
  have h3 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2)
  rw [hθ] at h3
  have : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [pow_one] at this
  omega

omit [Finite L] in
/-- Proportional powers of the generator, with exponents below `q² + q + 1`, are equal. -/
theorem exp_eq_of_proportional {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q) (ι : K →+* L)
    {θ : Lˣ} (hθ : orderOf θ = q ^ 3 - 1) {a b : ℕ} (ha : a < q ^ 2 + q + 1)
    (hb : b < q ^ 2 + q + 1) {μ : K} (hμ : μ ≠ 0) (h : (θ : L) ^ a = ι μ * (θ : L) ^ b) :
    a = b := by
  have hμ1 : μ ^ (q - 1) = 1 := pow_card_sub_one hK hμ
  have h2 : (θ : L) ^ (a * (q - 1)) = (θ : L) ^ (b * (q - 1)) := by
    rw [pow_mul, pow_mul, h, mul_pow, ← map_pow, hμ1, map_one, one_mul]
  have h3 : θ ^ (a * (q - 1)) = θ ^ (b * (q - 1)) := Units.ext (by simpa using h2)
  rw [pow_eq_pow_iff_modEq, hθ, cube_sub_one' hq] at h3
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.mul_right_cancel' (by omega) h3) ha hb

/-- `1, θ, θ²` are linearly independent over the image of `K`. -/
theorem lin_indep3 {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q) (ι : K →+* L) {θ : Lˣ}
    (hθ : orderOf θ = q ^ 3 - 1) {x y z x' y' z' : K}
    (h : ι x + ι y * θ + ι z * (θ : L) ^ 2 = ι x' + ι y' * θ + ι z' * (θ : L) ^ 2) :
    x = x' ∧ y = y' ∧ z = z' := by
  classical
  haveI : Fintype K := Fintype.ofFinite _
  by_cases hz : z = z'
  · subst hz
    by_cases hy : y = y'
    · subst hy
      exact ⟨ι.injective (by linear_combination h), rfl, rfl⟩
    · exfalso
      apply gen_not_base hq hK ι hθ ((x' - x) / (y - y'))
      have hne : ι y - ι y' ≠ 0 := by
        rw [← map_sub]
        intro h0
        exact hy (sub_eq_zero.mp (ι.injective (by rw [h0, map_zero])))
      rw [map_div₀, map_sub, map_sub, eq_div_iff hne]
      linear_combination h
  · exfalso
    have hne : ι z - ι z' ≠ 0 := by
      rw [← map_sub]
      intro h0
      exact hz (sub_eq_zero.mp (ι.injective (by rw [h0, map_zero])))
    have hsq : (θ : L) ^ 2 = ι ((x' - x) / (z - z')) + ι ((y' - y) / (z - z')) * θ := by
      rw [map_div₀, map_div₀, map_sub, map_sub, map_sub]
      field_simp
      linear_combination h
    have hpow : ∀ k : ℕ, ∃ u v : K, (θ : L) ^ k = ι u + ι v * θ := by
      intro k
      induction k with
      | zero => exact ⟨1, 0, by simp⟩
      | succ k ih =>
        obtain ⟨u, v, huv⟩ := ih
        refine ⟨v * ((x' - x) / (z - z')), u + v * ((y' - y) / (z - z')), ?_⟩
        rw [pow_succ, huv, map_mul, map_add, map_mul]
        linear_combination (ι v) * hsq
    have hinj : Set.InjOn (fun k : ℕ => (θ : L) ^ k) (range (q ^ 3 - 1)) := by
      intro i hi j hj hij
      rw [coe_range, Set.mem_Iio] at hi hj
      exact pow_injOn_Iio_orderOf (x := θ) (by rw [Set.mem_Iio, hθ]; exact hi)
        (by rw [Set.mem_Iio, hθ]; exact hj) (Units.ext (by simpa using hij))
    have hmaps : Set.MapsTo (fun k : ℕ => (θ : L) ^ k) (range (q ^ 3 - 1))
        ((univ : Finset (K × K)).image (fun w => ι w.1 + ι w.2 * θ)) := by
      intro k _
      obtain ⟨u, v, huv⟩ := hpow k
      rw [coe_image]
      exact ⟨(u, v), by simp, huv.symm⟩
    have h1 := card_le_card_of_injOn _ hmaps hinj
    rw [card_range] at h1
    have h2 := card_image_le (s := (univ : Finset (K × K))) (f := fun w => ι w.1 + ι w.2 * θ)
    rw [card_univ, Fintype.card_prod, Fintype.card_eq_nat_card, hK] at h2
    have h3 : q * q * 2 ≤ q * q * q := Nat.mul_le_mul_left _ hq
    have h4 : q ^ 3 = q * q * q := by ring
    have h5 : 2 * 2 ≤ q * q := Nat.mul_le_mul hq hq
    omega

omit [Finite K] in
/-- Two nonzero vectors of `K²` with vanishing determinant are proportional. -/
theorem proportional {x y x' y' : K} (h0 : ¬ (x = 0 ∧ y = 0)) (h0' : ¬ (x' = 0 ∧ y' = 0))
    (h : x * y' = y * x') : ∃ ν : K, ν ≠ 0 ∧ x' = ν * x ∧ y' = ν * y := by
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := fun hy => h0 ⟨rfl, hy⟩
    have hx' : x' = 0 := by
      rw [zero_mul] at h
      rcases mul_eq_zero.mp h.symm with h | h
      · exact absurd h hy
      · exact h
    have hy' : y' ≠ 0 := fun hy' => h0' ⟨hx', hy'⟩
    refine ⟨y' / y, div_ne_zero hy' hy, by rw [hx', mul_zero], ?_⟩
    field_simp
  · have hx' : x' ≠ 0 := by
      intro hx'
      apply h0'
      refine ⟨hx', ?_⟩
      rw [hx', mul_zero] at h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hx
      · exact h
    refine ⟨x' / x, div_ne_zero hx' hx, by field_simp, ?_⟩
    field_simp
    linear_combination h

theorem exists_dlog {θ : Lˣ} (hgen : ∀ x : Lˣ, x ∈ Submonoid.powers θ) (u : Lˣ) :
    ∃ a, a < orderOf θ ∧ θ ^ a = u := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (hgen u)
  exact ⟨n % orderOf θ, Nat.mod_lt _ (orderOf_pos θ), by rw [pow_mod_orderOf, hn]⟩

omit [Finite L] in
theorem shift_ne_zero {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q) (ι : K →+* L) {θ : Lˣ}
    (hθ : orderOf θ = q ^ 3 - 1) (c : K) : (θ : L) + ι c ≠ 0 := by
  intro h0
  apply gen_not_base hq hK ι hθ (-c)
  rw [map_neg]
  linear_combination h0

/-- Singer over a field `K` with `q` elements inside `L` with `q³`: `q + 1` residues modulo
`q² + q + 1` forming a Sidon set, hence `f m ≤ (m-1) q` for `m ≤ q + 1`. -/
theorem f_le_singer_general {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q) (hL : Nat.card L = q ^ 3)
    (ι : K →+* L) {m : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q + 1) : f m ≤ (m - 1) * q := by
  classical
  haveI : Fintype K := Fintype.ofFinite _
  have hn : 0 < q ^ 2 + q + 1 := by positivity
  obtain ⟨θ, hgen⟩ := IsCyclic.exists_monoid_generator (α := Lˣ)
  have hθ : orderOf θ = q ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hgen, Nat.card_units, hL]
  choose dl hdl_lt hdl_pow using exists_dlog hgen
  let u : K → Lˣ := fun c => Units.mk0 _ (shift_ne_zero hq hK ι hθ c)
  have hu : ∀ c, (u c : L) = θ + ι c := fun c => rfl
  have hcoord : ∀ c : K, ∃ μ : K, μ ≠ 0 ∧
      (θ : L) ^ (dl (u c) % (q ^ 2 + q + 1)) = ι (μ * c) + ι μ * θ := by
    intro c
    have hsplit : θ ^ dl (u c)
        = θ ^ ((q ^ 2 + q + 1) * (dl (u c) / (q ^ 2 + q + 1))) * θ ^ (dl (u c) % (q ^ 2 + q + 1)) := by
      rw [← pow_add, Nat.div_add_mod]
    have hlam : ((θ ^ ((q ^ 2 + q + 1) * (dl (u c) / (q ^ 2 + q + 1))))⁻¹) ^ (q - 1) = 1 := by
      rw [inv_pow, ← pow_mul, show (q ^ 2 + q + 1) * (dl (u c) / (q ^ 2 + q + 1)) * (q - 1)
        = (q ^ 3 - 1) * (dl (u c) / (q ^ 2 + q + 1)) by rw [cube_sub_one' hq]; ring,
        pow_mul, ← hθ, pow_orderOf_eq_one, one_pow, inv_one]
    obtain ⟨μ, hμ⟩ := mem_base_of_pow_eq_one hq hK ι hlam
    refine ⟨μ, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero] at hμ
      exact Units.ne_zero _ hμ
    · have h1 : θ ^ (dl (u c) % (q ^ 2 + q + 1))
          = (θ ^ ((q ^ 2 + q + 1) * (dl (u c) / (q ^ 2 + q + 1))))⁻¹ * θ ^ dl (u c) := by
        rw [hsplit, inv_mul_cancel_left]
      have hK1 := congrArg Units.val h1
      rw [Units.val_mul, hμ, hdl_pow, hu, Units.val_pow_eq_pow_val] at hK1
      rw [hK1, map_mul]
      ring
  set D : Finset ℕ := insert 0 ((univ : Finset K).image
    (fun c => dl (u c) % (q ^ 2 + q + 1))) with hD
  have hcoordD : ∀ a ∈ D, ∃ x y : K, ¬ (x = 0 ∧ y = 0) ∧ (θ : L) ^ a = ι x + ι y * θ := by
    intro a ha
    rw [hD, mem_insert, mem_image] at ha
    rcases ha with rfl | ⟨c, _, rfl⟩
    · exact ⟨1, 0, by simp, by simp⟩
    · obtain ⟨μ, hμ, hc⟩ := hcoord c
      exact ⟨μ * c, μ, fun h => hμ h.2, hc⟩
  have hDlt : ∀ a ∈ D, a < q ^ 2 + q + 1 := by
    intro a ha
    rw [hD, mem_insert, mem_image] at ha
    rcases ha with rfl | ⟨c, _, rfl⟩
    · exact hn
    · exact Nat.mod_lt _ hn
  have hr_inj : Function.Injective (fun c => dl (u c) % (q ^ 2 + q + 1)) := by
    intro c c' h
    obtain ⟨μ, hμ, hc⟩ := hcoord c
    obtain ⟨μ', hμ', hc'⟩ := hcoord c'
    simp only at h
    have : ι (μ * c) + ι μ * θ + ι 0 * (θ : L) ^ 2
        = ι (μ' * c') + ι μ' * θ + ι 0 * (θ : L) ^ 2 := by
      rw [map_zero, zero_mul, add_zero, add_zero, ← hc, ← hc', h]
    obtain ⟨h1, h2, _⟩ := lin_indep3 hq hK ι hθ this
    subst h2
    exact mul_left_cancel₀ hμ h1
  have h0D : 0 ∉ (univ : Finset K).image (fun c => dl (u c) % (q ^ 2 + q + 1)) := by
    rw [mem_image]
    rintro ⟨c, _, hc0⟩
    obtain ⟨μ, hμ, hc⟩ := hcoord c
    rw [hc0, pow_zero] at hc
    have : ι 1 + ι 0 * θ + ι 0 * (θ : L) ^ 2 = ι (μ * c) + ι μ * θ + ι 0 * (θ : L) ^ 2 := by
      rw [map_zero, map_one]
      linear_combination hc
    obtain ⟨_, h2, _⟩ := lin_indep3 hq hK ι hθ this
    exact hμ h2.symm
  have hDcard : D.card = q + 1 := by
    rw [hD, card_insert_of_notMem h0D, card_image_of_injective _ hr_inj, card_univ,
      Fintype.card_eq_nat_card, hK]
  have hsid : SidonMod (q ^ 2 + q + 1) D := by
    intro a ha b hb c hc d hd habcd
    obtain ⟨xa, ya, h0a, hea⟩ := hcoordD a ha
    obtain ⟨xb, yb, h0b, heb⟩ := hcoordD b hb
    obtain ⟨xc, yc, h0c, hec⟩ := hcoordD c hc
    obtain ⟨xd, yd, h0d, hed⟩ := hcoordD d hd
    have hmod : (a + b) * (q - 1) ≡ (c + d) * (q - 1) [MOD (q ^ 2 + q + 1) * (q - 1)] :=
      Nat.ModEq.mul_right' _ habcd
    have hpow : θ ^ ((a + b) * (q - 1)) = θ ^ ((c + d) * (q - 1)) := by
      rw [pow_eq_pow_iff_modEq, hθ, cube_sub_one' hq]; exact hmod
    have hlam : (θ ^ (a + b) * (θ ^ (c + d))⁻¹) ^ (q - 1) = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, hpow, mul_inv_cancel]
    obtain ⟨μ, hμ⟩ := mem_base_of_pow_eq_one hq hK ι hlam
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hμ
      exact Units.ne_zero _ hμ
    have hK0 : (θ : L) ^ a * (θ : L) ^ b = ι μ * ((θ : L) ^ c * (θ : L) ^ d) := by
      have h1 : θ ^ (a + b) = (θ ^ (a + b) * (θ ^ (c + d))⁻¹) * θ ^ (c + d) := by
        rw [inv_mul_cancel_right]
      have h2 := congrArg Units.val h1
      rw [Units.val_mul, hμ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_add,
        pow_add] at h2
      exact h2
    have hK2 := hK0
    rw [hea, heb, hec, hed] at hK2
    have hlin : ι (xa * xb) + ι (xa * yb + ya * xb) * θ + ι (ya * yb) * (θ : L) ^ 2
        = ι (μ * (xc * xd)) + ι (μ * (xc * yd + yc * xd)) * θ
          + ι (μ * (yc * yd)) * (θ : L) ^ 2 := by
      simp only [map_mul, map_add]
      linear_combination hK2
    obtain ⟨e1, e2, e3⟩ := lin_indep3 hq hK ι hθ hlin
    have hkey : μ * ((xa * yc - ya * xc) * (xa * yd - ya * xd)) = 0 := by
      linear_combination (-(ya ^ 2)) * e1 + (xa * ya) * e2 + (-(xa ^ 2)) * e3
    have hkey' := (mul_eq_zero.mp hkey).resolve_left hμ0
    have hprop : ∀ {e : ℕ} {xe ye : K}, e ∈ D → ¬ (xe = 0 ∧ ye = 0) →
        (θ : L) ^ e = ι xe + ι ye * θ → xa * ye = ya * xe → a = e := by
      intro e xe ye he h0e hee hdet
      obtain ⟨ν, hν, hx, hy⟩ := proportional h0a h0e hdet
      refine (exp_eq_of_proportional hq hK ι hθ (hDlt e he) (hDlt a ha) hν ?_).symm
      rw [hee, hea, hx, hy, map_mul, map_mul]
      ring
    have hne : (θ : L) ^ a ≠ 0 := pow_ne_zero _ θ.ne_zero
    rcases mul_eq_zero.mp hkey' with h | h
    · have hac : a = c := hprop hc h0c hec (sub_eq_zero.mp h)
      subst hac
      have hbd : (θ : L) ^ b = ι μ * (θ : L) ^ d :=
        mul_left_cancel₀ hne (hK0.trans (by ring))
      exact Or.inl ⟨rfl, exp_eq_of_proportional hq hK ι hθ (hDlt b hb) (hDlt d hd) hμ0 hbd⟩
    · have had : a = d := hprop hd h0d hed (sub_eq_zero.mp h)
      subst had
      have hbc : (θ : L) ^ b = ι μ * (θ : L) ^ c :=
        mul_left_cancel₀ hne (hK0.trans (by ring))
      exact Or.inr ⟨rfl, exp_eq_of_proportional hq hK ι hθ (hDlt b hb) (hDlt c hc) hμ0 hbc⟩
  refine f_le_of_sidonMod hn D hDlt hsid hm ?_ ?_
  · have : (m - 1) * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
    have h4 : q ^ 2 = q * q := by ring
    omega
  · rw [hDcard]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e : (q + 1) * (k * q + 1) + k = k * (q ^ 2 + q + 1) + (q + 1) := by ring
    omega

end SingerGeneral

/-- Singer for a prime power `q = p^k`: `GF(q) = GaloisField p k` inside `GaloisField p (3k)`. -/
theorem f_le_singer_pp {q m : ℕ} (hq : IsPrimePow q) (hm : 1 ≤ m) (hmq : m ≤ q + 1) :
    f m ≤ (m - 1) * q := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  haveI := Fact.mk hp
  have hK : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by omega)
  have hL : Nat.card (GaloisField p (3 * k)) = (p ^ k) ^ 3 := by
    rw [GaloisField.card p (3 * k) (by omega)]; ring
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := GaloisField p k)
    (L := GaloisField p (3 * k))
    (by rw [GaloisField.finrank p (by omega), GaloisField.finrank p (by omega)]
        exact Dvd.intro_left 3 rfl)
  have hq2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  exact f_le_singer_general hq2 hK hL φ.toRingHom hm hmq

theorem primePowGe_spec {m : ℕ} (hm : 1 ≤ m) : IsPrimePow (primePowGe m) ∧ m ≤ primePowGe m := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  rw [primePowGe]
  split
  next d heq =>
    have hd := List.find?_some heq
    exact ⟨of_decide_eq_true hd, by omega⟩
  next heq =>
    exfalso
    have hmem : p - m ∈ List.range (m + 1) := by
      rw [List.mem_range]; omega
    have hnone := List.find?_eq_none.mp heq _ hmem
    have hval : m + (p - m) = p := by omega
    rw [hval] at hnone
    exact absurd (decide_eq_true hp.isPrimePow) hnone

theorem singerPPLen_valid : UpperBoundHolds f singerPPLen := by
  intro m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [f, nMin]
    · have h := f_le_binRuler 1 (by simp)
      simpa [singerPPLen] using h
  · obtain ⟨hq, hle⟩ := primePowGe_spec (m := m - 1) (by omega)
    exact f_le_singer_pp hq (by omega) (by omega)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Golomb.Upper.V010.valid singerPPLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V010.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V010.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 33) (by decide)
    (by decide +kernel)

end SqueezeBench.Golomb.Upper.V011
