import SqueezeBench.Problems.Golomb.Records.Upper.V009.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V008.Proof

-- Golomb upper-bound record V009 — validity.
-- `K = GaloisField p 2` has `p²` elements and cyclic unit group; let `θ` generate it, so
-- `orderOf θ = p² - 1`. Then `θ ∉ GF(p)` (else `θ^(p-1) = 1`), so `1, θ` are linearly
-- independent over `ZMod p` (`lin_indep`), and every `θ + c`, `c : ZMod p`, is a unit with a
-- discrete logarithm `a < p² - 1`. If `a + b ≡ c + d (mod p² - 1)` for four such logarithms
-- then `(θ + x)(θ + y) = (θ + z)(θ + w)` in `K`; comparing coefficients of `1` and `θ` gives
-- `xy = zw`, `x + y = z + w`, hence `{x, y} = {z, w}` and `{a, b} = {c, d}`: the `p` logarithms
-- are Sidon modulo `p² - 1` and V008's `f_le_of_sidonMod` rotates them into a window of
-- length `⌊(m-1)(p²-1)/p⌋`. `primeGe_spec` is V002's `nextPrime_spec` with `≥` in place of `>`.

namespace SqueezeBench.Golomb.Upper.V009

open SqueezeBench Finset
open SqueezeBench.Golomb.Upper.V008 (SidonMod f_le_of_sidonMod)

section BoseChowla

variable {p : ℕ} [hp : Fact p.Prime]

theorem card_units_gf : Nat.card (GaloisField p 2)ˣ = p ^ 2 - 1 := by
  rw [Nat.card_units, GaloisField.card p 2 (by norm_num)]

theorem base_injective : Function.Injective (algebraMap (ZMod p) (GaloisField p 2)) :=
  (algebraMap (ZMod p) (GaloisField p 2)).injective

/-- A generator of the units of `GF(p²)` lies outside the prime field. -/
theorem gen_not_base {θ : (GaloisField p 2)ˣ} (hθ : orderOf θ = p ^ 2 - 1) (c : ZMod p) :
    (θ : GaloisField p 2) ≠ algebraMap (ZMod p) (GaloisField p 2) c := by
  intro h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact θ.ne_zero h
  have h1 : (θ : GaloisField p 2) ^ (p - 1) = 1 := by
    rw [h, ← map_pow, ZMod.pow_card_sub_one_eq_one hc, map_one]
  have h2 : θ ^ (p - 1) = 1 := Units.ext (by simpa using h1)
  have h3 := Nat.le_of_dvd (by have := hp.out.two_le; omega) (orderOf_dvd_of_pow_eq_one h2)
  rw [hθ] at h3
  have hp2 := hp.out.two_le
  have : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
  rw [sq] at h3
  omega

/-- `1, θ` are linearly independent over the prime field. -/
theorem lin_indep {θ : (GaloisField p 2)ˣ} (hθ : orderOf θ = p ^ 2 - 1) {x y x' y' : ZMod p}
    (h : algebraMap (ZMod p) (GaloisField p 2) x + algebraMap (ZMod p) (GaloisField p 2) y * θ
      = algebraMap (ZMod p) (GaloisField p 2) x' + algebraMap (ZMod p) (GaloisField p 2) y' * θ) :
    x = x' ∧ y = y' := by
  by_cases hy : y = y'
  · subst hy
    exact ⟨base_injective (by linear_combination h), rfl⟩
  · exfalso
    apply gen_not_base hθ ((x' - x) / (y - y'))
    have hne : algebraMap (ZMod p) (GaloisField p 2) y
        - algebraMap (ZMod p) (GaloisField p 2) y' ≠ 0 := by
      rw [← map_sub]
      intro h0
      exact hy (sub_eq_zero.mp (base_injective (by rw [h0, map_zero])))
    rw [map_div₀, map_sub, map_sub, eq_div_iff hne]
    linear_combination h

theorem exists_dlog {θ : (GaloisField p 2)ˣ} (hgen : ∀ x : (GaloisField p 2)ˣ, x ∈ Submonoid.powers θ)
    (u : (GaloisField p 2)ˣ) : ∃ a, a < orderOf θ ∧ θ ^ a = u := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (hgen u)
  exact ⟨n % orderOf θ, Nat.mod_lt _ (orderOf_pos θ), by rw [pow_mod_orderOf, hn]⟩

/-- `θ + c` is a unit. -/
theorem shift_ne_zero {θ : (GaloisField p 2)ˣ} (hθ : orderOf θ = p ^ 2 - 1) (c : ZMod p) :
    (θ : GaloisField p 2) + algebraMap (ZMod p) (GaloisField p 2) c ≠ 0 := by
  intro h0
  apply gen_not_base hθ (-c)
  rw [map_neg]
  linear_combination h0

/-- Bose–Chowla: `p` residues modulo `p² - 1` forming a Sidon set, hence `f m ≤ ⌊(m-1)(p²-1)/p⌋`. -/
theorem f_le_bose_chowla {m : ℕ} (hm : 1 ≤ m) (hmp : m ≤ p) :
    f m ≤ (m - 1) * (p ^ 2 - 1) / p := by
  have hp2 := hp.out.two_le
  have hn : 0 < p ^ 2 - 1 := by
    have : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    rw [sq]; omega
  obtain ⟨θ, hgen⟩ := IsCyclic.exists_monoid_generator (α := (GaloisField p 2)ˣ)
  have hθ : orderOf θ = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hgen, card_units_gf]
  choose dl hdl_lt hdl_pow using exists_dlog hgen
  let u : ZMod p → (GaloisField p 2)ˣ := fun c => Units.mk0 _ (shift_ne_zero hθ c)
  have hu : ∀ c, (u c : GaloisField p 2) = θ + algebraMap (ZMod p) (GaloisField p 2) c :=
    fun c => rfl
  have hu_inj : Function.Injective u := by
    intro c c' h
    have := congrArg Units.val h
    rw [hu, hu] at this
    exact base_injective (add_left_cancel this)
  have hdl_inj : Function.Injective (fun c => dl (u c)) := by
    intro c c' h
    apply hu_inj
    rw [← hdl_pow (u c), ← hdl_pow (u c')]
    exact congrArg (θ ^ ·) h
  have hsid : SidonMod (p ^ 2 - 1) ((univ : Finset (ZMod p)).image (fun c => dl (u c))) := by
    intro a ha b hb c hc d hd habcd
    simp only [mem_image, mem_univ, true_and] at ha hb hc hd
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    obtain ⟨z, rfl⟩ := hc
    obtain ⟨w, rfl⟩ := hd
    have hpow : θ ^ (dl (u x) + dl (u y)) = θ ^ (dl (u z) + dl (u w)) := by
      rw [pow_eq_pow_iff_modEq, hθ]; exact habcd
    rw [pow_add, pow_add, hdl_pow, hdl_pow, hdl_pow, hdl_pow] at hpow
    have hK := congrArg Units.val hpow
    rw [Units.val_mul, Units.val_mul, hu, hu, hu, hu] at hK
    have hlin : algebraMap (ZMod p) (GaloisField p 2) (x * y)
        + algebraMap (ZMod p) (GaloisField p 2) (x + y) * θ
        = algebraMap (ZMod p) (GaloisField p 2) (z * w)
        + algebraMap (ZMod p) (GaloisField p 2) (z + w) * θ := by
      rw [map_mul, map_mul, map_add, map_add]
      linear_combination hK
    obtain ⟨hprod, hsum⟩ := lin_indep hθ hlin
    have hz : (x - z) * (x - w) = 0 := by linear_combination x * hsum - hprod
    rcases mul_eq_zero.mp hz with h | h
    · have hxz : x = z := sub_eq_zero.mp h
      have hyw : y = w := by linear_combination hsum - hxz
      subst hxz; subst hyw
      exact Or.inl ⟨rfl, rfl⟩
    · have hxw : x = w := sub_eq_zero.mp h
      have hyz : y = z := by linear_combination hsum - hxw
      subst hxw; subst hyz
      exact Or.inr ⟨rfl, rfl⟩
  refine f_le_of_sidonMod hn _ ?_ hsid hm ?_ ?_
  · intro a ha
    simp only [mem_image, mem_univ, true_and] at ha
    obtain ⟨x, rfl⟩ := ha
    rw [← hθ]; exact hdl_lt _
  · exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right (by omega) hn)
  · rw [card_image_of_injective _ hdl_inj, card_univ, ZMod.card]
    exact Nat.lt_mul_div_succ _ (by omega)

end BoseChowla

theorem primeGe_spec {m : ℕ} (hm : 1 ≤ m) : (primeGe m).Prime ∧ m ≤ primeGe m := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  rw [primeGe]
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
    exact absurd (decide_eq_true hp) hnone

theorem bcLen_valid : UpperBoundHolds f bcLen := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [f, nMin]
  · obtain ⟨hp, hle⟩ := primeGe_spec hm
    haveI := Fact.mk hp
    exact f_le_bose_chowla hm hle

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Golomb.Upper.V008.valid bcLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V008.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V008.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 31) (by decide)
    (by decide +kernel)

end SqueezeBench.Golomb.Upper.V009
