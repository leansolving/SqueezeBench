import SqueezeBench.Problems.Golomb.Records.Upper.V010.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V009.Proof

-- Golomb upper-bound record V010 — validity.
-- `K = GaloisField p 3`, `θ` a generator of `Kˣ` (order `p³ - 1 = (p²+p+1)(p-1)`), `ι` the
-- prime field. Three facts about `K`: the units with `x^(p-1) = 1` are exactly `ι(GF(p)ˣ)`
-- (`mem_base_of_pow_eq_one`: a cyclic group has at most `p - 1` of them); `1, θ, θ²` are
-- independent over `GF(p)` (`lin_indep3`: otherwise all `p³ - 1` distinct powers of `θ` would
-- lie in `GF(p) + GF(p)θ`, a set of size `p²`); and `θᵃ = ι μ · θᵇ` with `a, b < p² + p + 1`
-- forces `a = b` (`exp_eq_of_proportional`: raise to the power `p - 1`).
-- The Singer set `D` consists of `0` and the residues `dlog(θ + c) mod (p²+p+1)`, `c ∈ GF(p)`;
-- each `θᵃ`, `a ∈ D`, is `ι x + ι y·θ` with `(x, y) ≠ 0` because `θ^(p²+p+1)` has `(p-1)`-th
-- power `1`. If `a + b ≡ c + d` then `θᵃθᵇ = ι μ · θᶜθᵈ`, and comparing coefficients gives
-- `(xₐy_c - yₐx_c)(xₐy_d - yₐx_d) = 0`, so `(xₐ, yₐ)` is proportional to `(x_c, y_c)` or
-- `(x_d, y_d)` and `a = c` or `a = d`; the other exponent follows by cancelling. V008's
-- `f_le_of_sidonMod` with `n = p² + p + 1`, `k = p + 1`, `L = (m-1) p` finishes.

namespace SqueezeBench.Golomb.Upper.V010

open SqueezeBench Finset
open SqueezeBench.Golomb.Upper.V008 (SidonMod f_le_of_sidonMod)

section Singer

variable {p : ℕ} [hp : Fact p.Prime]

/-- The prime field inside `GF(p³)`. -/
noncomputable abbrev ι (p : ℕ) [Fact p.Prime] : ZMod p →+* GaloisField p 3 :=
  algebraMap (ZMod p) (GaloisField p 3)

theorem card_units_gf3 : Nat.card (GaloisField p 3)ˣ = p ^ 3 - 1 := by
  rw [Nat.card_units, GaloisField.card p 3 (by norm_num)]

theorem cube_sub_one : p ^ 3 - 1 = (p ^ 2 + p + 1) * (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have h : (q + 1) ^ 3 = ((q + 1) ^ 2 + (q + 1) + 1) * q + 1 := by ring
  simp only [Nat.add_sub_cancel]
  omega

/-- Units of `GF(p³)` with `x^(p-1) = 1` lie in the prime field: a cyclic group has at most
`p - 1` such elements, and the prime field already supplies `p - 1`. -/
theorem mem_base_of_pow_eq_one {x : (GaloisField p 3)ˣ} (h : x ^ (p - 1) = 1) :
    ∃ c : ZMod p, (x : GaloisField p 3) = ι p c := by
  classical
  haveI : Fintype (GaloisField p 3)ˣ := Fintype.ofFinite _
  have hp2 := hp.out.two_le
  have hT := IsCyclic.card_pow_eq_one_le (α := (GaloisField p 3)ˣ) (n := p - 1) (by omega)
  let φ : (ZMod p)ˣ →* (GaloisField p 3)ˣ := Units.map (ι p).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (ι p).injective
  have hsub : (univ : Finset (ZMod p)ˣ).image φ ⊆ univ.filter (fun a => a ^ (p - 1) = 1) := by
    intro a ha
    rw [mem_image] at ha
    obtain ⟨c, _, rfl⟩ := ha
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hc : c ^ (p - 1) = 1 := by rw [← ZMod.card_units p]; exact pow_card_eq_one
    rw [← map_pow, hc, map_one]
  have hcard : (univ.filter (fun a : (GaloisField p 3)ˣ => a ^ (p - 1) = 1)).card
      ≤ ((univ : Finset (ZMod p)ˣ).image φ).card := by
    rw [card_image_of_injective _ hφ, card_univ, ZMod.card_units]
    exact hT
  have heq := eq_of_subset_of_card_le hsub hcard
  have hx : x ∈ univ.filter (fun a : (GaloisField p 3)ˣ => a ^ (p - 1) = 1) := by
    rw [mem_filter]; exact ⟨mem_univ _, h⟩
  rw [← heq, mem_image] at hx
  obtain ⟨c, _, rfl⟩ := hx
  exact ⟨c, rfl⟩

/-- A generator of the units lies outside the prime field. -/
theorem gen_not_base3 {θ : (GaloisField p 3)ˣ} (hθ : orderOf θ = p ^ 3 - 1) (c : ZMod p) :
    (θ : GaloisField p 3) ≠ ι p c := by
  intro h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact θ.ne_zero h
  have h1 : (θ : GaloisField p 3) ^ (p - 1) = 1 := by
    rw [h, ← map_pow, ZMod.pow_card_sub_one_eq_one hc, map_one]
  have h2 : θ ^ (p - 1) = 1 := Units.ext (by simpa using h1)
  have hp2 := hp.out.two_le
  have h3 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h2)
  rw [hθ] at h3
  have : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [pow_one] at this
  omega

/-- Proportional powers of the generator, with exponents below `p² + p + 1`, are equal. -/
theorem exp_eq_of_proportional {θ : (GaloisField p 3)ˣ} (hθ : orderOf θ = p ^ 3 - 1)
    {a b : ℕ} (ha : a < p ^ 2 + p + 1) (hb : b < p ^ 2 + p + 1) {μ : ZMod p} (hμ : μ ≠ 0)
    (h : (θ : GaloisField p 3) ^ a = ι p μ * (θ : GaloisField p 3) ^ b) : a = b := by
  have hμ1 : μ ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hμ
  have h2 : (θ : GaloisField p 3) ^ (a * (p - 1)) = (θ : GaloisField p 3) ^ (b * (p - 1)) := by
    rw [pow_mul, pow_mul, h, mul_pow, ← map_pow, hμ1, map_one, one_mul]
  have h3 : θ ^ (a * (p - 1)) = θ ^ (b * (p - 1)) := Units.ext (by simpa using h2)
  rw [pow_eq_pow_iff_modEq, hθ, cube_sub_one] at h3
  have hp2 := hp.out.two_le
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.mul_right_cancel' (by omega) h3) ha hb

/-- `1, θ, θ²` are linearly independent over the prime field. -/
theorem lin_indep3 {θ : (GaloisField p 3)ˣ} (hθ : orderOf θ = p ^ 3 - 1) {x y z x' y' z' : ZMod p}
    (h : ι p x + ι p y * θ + ι p z * (θ : GaloisField p 3) ^ 2
      = ι p x' + ι p y' * θ + ι p z' * (θ : GaloisField p 3) ^ 2) :
    x = x' ∧ y = y' ∧ z = z' := by
  classical
  by_cases hz : z = z'
  · subst hz
    by_cases hy : y = y'
    · subst hy
      exact ⟨(ι p).injective (by linear_combination h), rfl, rfl⟩
    · exfalso
      apply gen_not_base3 hθ ((x' - x) / (y - y'))
      have hne : ι p y - ι p y' ≠ 0 := by
        rw [← map_sub]
        intro h0
        exact hy (sub_eq_zero.mp ((ι p).injective (by rw [h0, map_zero])))
      rw [map_div₀, map_sub, map_sub, eq_div_iff hne]
      linear_combination h
  · exfalso
    have hne : ι p z - ι p z' ≠ 0 := by
      rw [← map_sub]
      intro h0
      exact hz (sub_eq_zero.mp ((ι p).injective (by rw [h0, map_zero])))
    have hsq : (θ : GaloisField p 3) ^ 2
        = ι p ((x' - x) / (z - z')) + ι p ((y' - y) / (z - z')) * θ := by
      rw [map_div₀, map_div₀, map_sub, map_sub, map_sub]
      field_simp
      linear_combination h
    have hpow : ∀ k : ℕ, ∃ u v : ZMod p, (θ : GaloisField p 3) ^ k = ι p u + ι p v * θ := by
      intro k
      induction k with
      | zero => exact ⟨1, 0, by simp⟩
      | succ k ih =>
        obtain ⟨u, v, huv⟩ := ih
        refine ⟨v * ((x' - x) / (z - z')), u + v * ((y' - y) / (z - z')), ?_⟩
        rw [pow_succ, huv, map_mul, map_add, map_mul]
        linear_combination (ι p v) * hsq
    have hinj : Set.InjOn (fun k : ℕ => (θ : GaloisField p 3) ^ k) (range (p ^ 3 - 1)) := by
      intro i hi j hj hij
      rw [coe_range, Set.mem_Iio] at hi hj
      exact pow_injOn_Iio_orderOf (x := θ) (by rw [Set.mem_Iio, hθ]; exact hi)
        (by rw [Set.mem_Iio, hθ]; exact hj) (Units.ext (by simpa using hij))
    have hmaps : Set.MapsTo (fun k : ℕ => (θ : GaloisField p 3) ^ k) (range (p ^ 3 - 1))
        ((univ : Finset (ZMod p × ZMod p)).image (fun q => ι p q.1 + ι p q.2 * θ)) := by
      intro k _
      obtain ⟨u, v, huv⟩ := hpow k
      rw [coe_image]
      exact ⟨(u, v), by simp, huv.symm⟩
    have h1 := card_le_card_of_injOn _ hmaps hinj
    rw [card_range] at h1
    have h2 := card_image_le (s := (univ : Finset (ZMod p × ZMod p)))
      (f := fun q => ι p q.1 + ι p q.2 * θ)
    rw [card_univ, Fintype.card_prod, ZMod.card] at h2
    have hp2 := hp.out.two_le
    have h3 : p * p * 2 ≤ p * p * p := Nat.mul_le_mul_left _ hp2
    have h4 : p ^ 3 = p * p * p := by ring
    have h5 : 2 * 2 ≤ p * p := Nat.mul_le_mul hp2 hp2
    omega

/-- Two nonzero vectors of `GF(p)²` with vanishing determinant are proportional. -/
theorem proportional {x y x' y' : ZMod p} (h0 : ¬ (x = 0 ∧ y = 0)) (h0' : ¬ (x' = 0 ∧ y' = 0))
    (h : x * y' = y * x') : ∃ ν : ZMod p, ν ≠ 0 ∧ x' = ν * x ∧ y' = ν * y := by
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

theorem exists_dlog3 {θ : (GaloisField p 3)ˣ} (hgen : ∀ x : (GaloisField p 3)ˣ, x ∈ Submonoid.powers θ)
    (u : (GaloisField p 3)ˣ) : ∃ a, a < orderOf θ ∧ θ ^ a = u := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (hgen u)
  exact ⟨n % orderOf θ, Nat.mod_lt _ (orderOf_pos θ), by rw [pow_mod_orderOf, hn]⟩

theorem shift_ne_zero3 {θ : (GaloisField p 3)ˣ} (hθ : orderOf θ = p ^ 3 - 1) (c : ZMod p) :
    (θ : GaloisField p 3) + ι p c ≠ 0 := by
  intro h0
  apply gen_not_base3 hθ (-c)
  rw [map_neg]
  linear_combination h0

/-- Singer: `p + 1` residues modulo `p² + p + 1` forming a Sidon set, hence `f m ≤ (m-1) p`
for `m ≤ p + 1`. -/
theorem f_le_singer {m : ℕ} (hm : 1 ≤ m) (hmp : m ≤ p + 1) : f m ≤ (m - 1) * p := by
  classical
  have hp2 := hp.out.two_le
  have hn : 0 < p ^ 2 + p + 1 := by positivity
  obtain ⟨θ, hgen⟩ := IsCyclic.exists_monoid_generator (α := (GaloisField p 3)ˣ)
  have hθ : orderOf θ = p ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hgen, card_units_gf3]
  choose dl hdl_lt hdl_pow using exists_dlog3 hgen
  let u : ZMod p → (GaloisField p 3)ˣ := fun c => Units.mk0 _ (shift_ne_zero3 hθ c)
  have hu : ∀ c, (u c : GaloisField p 3) = θ + ι p c := fun c => rfl
  have hcoord : ∀ c : ZMod p, ∃ μ : ZMod p, μ ≠ 0 ∧
      (θ : GaloisField p 3) ^ (dl (u c) % (p ^ 2 + p + 1)) = ι p (μ * c) + ι p μ * θ := by
    intro c
    have hsplit : θ ^ dl (u c)
        = θ ^ ((p ^ 2 + p + 1) * (dl (u c) / (p ^ 2 + p + 1))) * θ ^ (dl (u c) % (p ^ 2 + p + 1)) := by
      rw [← pow_add, Nat.div_add_mod]
    have hlam : ((θ ^ ((p ^ 2 + p + 1) * (dl (u c) / (p ^ 2 + p + 1))))⁻¹) ^ (p - 1) = 1 := by
      rw [inv_pow, ← pow_mul, show (p ^ 2 + p + 1) * (dl (u c) / (p ^ 2 + p + 1)) * (p - 1)
        = (p ^ 3 - 1) * (dl (u c) / (p ^ 2 + p + 1)) by rw [cube_sub_one]; ring,
        pow_mul, ← hθ, pow_orderOf_eq_one, one_pow, inv_one]
    obtain ⟨μ, hμ⟩ := mem_base_of_pow_eq_one hlam
    refine ⟨μ, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero] at hμ
      exact Units.ne_zero _ hμ
    · have h1 : θ ^ (dl (u c) % (p ^ 2 + p + 1))
          = (θ ^ ((p ^ 2 + p + 1) * (dl (u c) / (p ^ 2 + p + 1))))⁻¹ * θ ^ dl (u c) := by
        rw [hsplit, inv_mul_cancel_left]
      have hK := congrArg Units.val h1
      rw [Units.val_mul, hμ, hdl_pow, hu, Units.val_pow_eq_pow_val] at hK
      rw [hK, map_mul]
      ring
  set D : Finset ℕ := insert 0 ((univ : Finset (ZMod p)).image
    (fun c => dl (u c) % (p ^ 2 + p + 1))) with hD
  have hcoordD : ∀ a ∈ D, ∃ x y : ZMod p, ¬ (x = 0 ∧ y = 0) ∧
      (θ : GaloisField p 3) ^ a = ι p x + ι p y * θ := by
    intro a ha
    rw [hD, mem_insert, mem_image] at ha
    rcases ha with rfl | ⟨c, _, rfl⟩
    · exact ⟨1, 0, by simp, by simp⟩
    · obtain ⟨μ, hμ, hc⟩ := hcoord c
      exact ⟨μ * c, μ, fun h => hμ h.2, hc⟩
  have hDlt : ∀ a ∈ D, a < p ^ 2 + p + 1 := by
    intro a ha
    rw [hD, mem_insert, mem_image] at ha
    rcases ha with rfl | ⟨c, _, rfl⟩
    · exact hn
    · exact Nat.mod_lt _ hn
  have hr_inj : Function.Injective (fun c => dl (u c) % (p ^ 2 + p + 1)) := by
    intro c c' h
    obtain ⟨μ, hμ, hc⟩ := hcoord c
    obtain ⟨μ', hμ', hc'⟩ := hcoord c'
    simp only at h
    have : ι p (μ * c) + ι p μ * θ + ι p 0 * (θ : GaloisField p 3) ^ 2
        = ι p (μ' * c') + ι p μ' * θ + ι p 0 * (θ : GaloisField p 3) ^ 2 := by
      rw [map_zero, zero_mul, add_zero, add_zero, ← hc, ← hc', h]
    obtain ⟨h1, h2, _⟩ := lin_indep3 hθ this
    subst h2
    exact mul_left_cancel₀ hμ h1
  have h0D : 0 ∉ (univ : Finset (ZMod p)).image (fun c => dl (u c) % (p ^ 2 + p + 1)) := by
    rw [mem_image]
    rintro ⟨c, _, hc0⟩
    obtain ⟨μ, hμ, hc⟩ := hcoord c
    rw [hc0, pow_zero] at hc
    have : ι p 1 + ι p 0 * θ + ι p 0 * (θ : GaloisField p 3) ^ 2
        = ι p (μ * c) + ι p μ * θ + ι p 0 * (θ : GaloisField p 3) ^ 2 := by
      rw [map_zero, map_one]
      linear_combination hc
    obtain ⟨_, h2, _⟩ := lin_indep3 hθ this
    exact hμ h2.symm
  have hDcard : D.card = p + 1 := by
    rw [hD, card_insert_of_notMem h0D, card_image_of_injective _ hr_inj, card_univ, ZMod.card]
  have hsid : SidonMod (p ^ 2 + p + 1) D := by
    intro a ha b hb c hc d hd habcd
    obtain ⟨xa, ya, h0a, hea⟩ := hcoordD a ha
    obtain ⟨xb, yb, h0b, heb⟩ := hcoordD b hb
    obtain ⟨xc, yc, h0c, hec⟩ := hcoordD c hc
    obtain ⟨xd, yd, h0d, hed⟩ := hcoordD d hd
    have hmod : (a + b) * (p - 1) ≡ (c + d) * (p - 1) [MOD (p ^ 2 + p + 1) * (p - 1)] :=
      Nat.ModEq.mul_right' _ habcd
    have hpow : θ ^ ((a + b) * (p - 1)) = θ ^ ((c + d) * (p - 1)) := by
      rw [pow_eq_pow_iff_modEq, hθ, cube_sub_one]; exact hmod
    have hlam : (θ ^ (a + b) * (θ ^ (c + d))⁻¹) ^ (p - 1) = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, hpow, mul_inv_cancel]
    obtain ⟨μ, hμ⟩ := mem_base_of_pow_eq_one hlam
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hμ
      exact Units.ne_zero _ hμ
    have hK0 : (θ : GaloisField p 3) ^ a * (θ : GaloisField p 3) ^ b
        = ι p μ * ((θ : GaloisField p 3) ^ c * (θ : GaloisField p 3) ^ d) := by
      have h1 : θ ^ (a + b) = (θ ^ (a + b) * (θ ^ (c + d))⁻¹) * θ ^ (c + d) := by
        rw [inv_mul_cancel_right]
      have h2 := congrArg Units.val h1
      rw [Units.val_mul, hμ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_add,
        pow_add] at h2
      exact h2
    have hK := hK0
    rw [hea, heb, hec, hed] at hK
    have hlin : ι p (xa * xb) + ι p (xa * yb + ya * xb) * θ
          + ι p (ya * yb) * (θ : GaloisField p 3) ^ 2
        = ι p (μ * (xc * xd)) + ι p (μ * (xc * yd + yc * xd)) * θ
          + ι p (μ * (yc * yd)) * (θ : GaloisField p 3) ^ 2 := by
      simp only [map_mul, map_add]
      linear_combination hK
    obtain ⟨e1, e2, e3⟩ := lin_indep3 hθ hlin
    have hkey : μ * ((xa * yc - ya * xc) * (xa * yd - ya * xd)) = 0 := by
      linear_combination (-(ya ^ 2)) * e1 + (xa * ya) * e2 + (-(xa ^ 2)) * e3
    have hkey' := (mul_eq_zero.mp hkey).resolve_left hμ0
    have hprop : ∀ {e : ℕ} {xe ye : ZMod p}, e ∈ D → ¬ (xe = 0 ∧ ye = 0) →
        (θ : GaloisField p 3) ^ e = ι p xe + ι p ye * θ → xa * ye = ya * xe → a = e := by
      intro e xe ye he h0e hee hdet
      obtain ⟨ν, hν, hx, hy⟩ := proportional h0a h0e hdet
      refine (exp_eq_of_proportional hθ (hDlt e he) (hDlt a ha) hν ?_).symm
      rw [hee, hea, hx, hy, map_mul, map_mul]
      ring
    have hne : (θ : GaloisField p 3) ^ a ≠ 0 := pow_ne_zero _ θ.ne_zero
    rcases mul_eq_zero.mp hkey' with h | h
    · have hac : a = c := hprop hc h0c hec (sub_eq_zero.mp h)
      subst hac
      have hbd : (θ : GaloisField p 3) ^ b = ι p μ * (θ : GaloisField p 3) ^ d :=
        mul_left_cancel₀ hne (hK0.trans (by ring))
      exact Or.inl ⟨rfl, exp_eq_of_proportional hθ (hDlt b hb) (hDlt d hd) hμ0 hbd⟩
    · have had : a = d := hprop hd h0d hed (sub_eq_zero.mp h)
      subst had
      have hbc : (θ : GaloisField p 3) ^ b = ι p μ * (θ : GaloisField p 3) ^ c :=
        mul_left_cancel₀ hne (hK0.trans (by ring))
      exact Or.inr ⟨rfl, exp_eq_of_proportional hθ (hDlt b hb) (hDlt c hc) hμ0 hbc⟩
  refine f_le_of_sidonMod hn D hDlt hsid hm ?_ ?_
  · have : (m - 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
    have h4 : p ^ 2 = p * p := by ring
    omega
  · rw [hDcard]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e : (p + 1) * (k * p + 1) + k = k * (p ^ 2 + p + 1) + (p + 1) := by ring
    omega

end Singer

theorem singerLen_valid : UpperBoundHolds f singerLen := by
  intro m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [f, nMin]
    · have h := f_le_binRuler 1 (by simp)
      simpa [singerLen] using h
  · obtain ⟨hq, hle⟩ := SqueezeBench.Golomb.Upper.V009.primeGe_spec (m := m - 1) (by omega)
    haveI := Fact.mk hq
    exact f_le_singer (by omega) (by omega)

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Golomb.Upper.V009.valid singerLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V009.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V009.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 30) (by decide)
    (by decide +kernel)

end SqueezeBench.Golomb.Upper.V010
