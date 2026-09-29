import SqueezeBench.Problems.Golomb.Records.Upper.V006.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V005.Proof

-- Golomb upper-bound record V006 — validity.
-- Ruzsa's ruler modulo `p(p-1)`: the mark of index `i < p - 1` is the residue that is `i` modulo
-- `p - 1` and `-gⁱ` modulo `p`, for a generator `g` of `(ZMod p)ˣ`. If four marks satisfy
-- `aᵢ + aⱼ = aₖ + aₗ`, reduction modulo `p - 1` gives `i + j ≡ k + l`, hence `gⁱgʲ = gᵏgˡ`
-- since `g` has order `p - 1`, and reduction modulo `p` gives `gⁱ + gʲ = gᵏ + gˡ`; so
-- `(gⁱ - gᵏ)(gⁱ - gˡ) = 0` in the field `ZMod p`, and `i ↦ gⁱ` is injective below `p - 1`.
-- `f_le_of_sidon` turns any Sidon set with at least `m` elements below `N` into `f m ≤ N - 1`
-- by passing to an `m`-element subset and its maximum. `nextPrime_spec` is V002's.

namespace SqueezeBench.Golomb.Upper.V006

open SqueezeBench Finset

/-- A Sidon set with at least `m` elements, all below `N`, gives `f m ≤ N - 1`. -/
theorem f_le_of_sidon {m N : ℕ} (hm : 1 ≤ m) (S : Finset ℕ) (hS : IsSidon S)
    (hcard : m ≤ S.card) (hN : ∀ x ∈ S, x < N) : f m ≤ N - 1 := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hcard
  have hne : T.Nonempty := by
    rw [← Finset.card_pos, hT]; omega
  have hLT : T.max' hne ∈ T := Finset.max'_mem T hne
  have hLN : T.max' hne < N := hN _ (hTS hLT)
  refine le_trans (f_le_of_mem (by simp only [nMin_eq]; omega) ⟨T, ?_, hT, ?_, hLT⟩) (by omega)
  · intro x hx
    rw [Finset.mem_range]
    have := Finset.le_max' T x hx
    omega
  · intro a ha b hb c hc d hd h
    exact hS a (hTS ha) b (hTS hb) c (hTS hc) d (hTS hd) h

/-- Ruzsa's mark of index `i`: the residue `≡ i (mod p-1)`, `≡ -gⁱ (mod p)`, below `p(p-1)`. -/
def ruzsaMark (p : ℕ) (g : ZMod p) (i : ℕ) : ℕ :=
  (p * i + (p - 1) * (g ^ i).val) % (p * (p - 1))

/-- Ruzsa's ruler: the `p - 1` marks of index `i < p - 1`. -/
def ruzsaRuler (p : ℕ) (g : ZMod p) : Finset ℕ := (range (p - 1)).image (ruzsaMark p g)

theorem ruzsaMark_lt {p : ℕ} (hp : 2 ≤ p) (g : ZMod p) (i : ℕ) :
    ruzsaMark p g i < p * (p - 1) :=
  Nat.mod_lt _ (Nat.mul_pos (by omega) (by omega))

theorem split_aux (p i v : ℕ) (hp : 1 ≤ p) :
    p * i + (p - 1) * v = (p - 1) * (i + v) + i := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- The index is recovered from the mark modulo `p - 1`. -/
theorem ruzsaMark_mod_sub_one {p : ℕ} (hp : 2 ≤ p) (g : ZMod p) {i : ℕ} (hi : i < p - 1) :
    ruzsaMark p g i % (p - 1) = i := by
  unfold ruzsaMark
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left _ rfl), split_aux p i _ (by omega), Nat.mul_add_mod,
    Nat.mod_eq_of_lt hi]

theorem ruzsaMark_modEq {p : ℕ} (hp : 2 ≤ p) (g : ZMod p) {i : ℕ} (hi : i < p - 1) :
    ruzsaMark p g i ≡ i [MOD p - 1] := by
  unfold Nat.ModEq
  rw [ruzsaMark_mod_sub_one hp g hi, Nat.mod_eq_of_lt hi]

/-- Modulo `p` the mark is `-gⁱ`. -/
theorem ruzsaMark_cast {p : ℕ} [Fact p.Prime] (g : ZMod p) (i : ℕ) :
    ((ruzsaMark p g i : ℕ) : ZMod p) = -(g ^ i) := by
  unfold ruzsaMark
  have hmod : (p * i + (p - 1) * (g ^ i).val) % (p * (p - 1))
      ≡ p * i + (p - 1) * (g ^ i).val [MOD p] :=
    (Nat.mod_modEq _ _).of_mul_right _
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  push_cast [Nat.cast_sub hp1]
  simp

theorem ruzsaMark_injOn {p : ℕ} (hp : 2 ≤ p) (g : ZMod p) :
    Set.InjOn (ruzsaMark p g) (range (p - 1)) := by
  intro i hi j hj h
  rw [coe_range, Set.mem_Iio] at hi hj
  rw [← ruzsaMark_mod_sub_one hp g hi, ← ruzsaMark_mod_sub_one hp g hj, h]

theorem ruzsaRuler_card {p : ℕ} (hp : 2 ≤ p) (g : ZMod p) : (ruzsaRuler p g).card = p - 1 := by
  rw [ruzsaRuler, card_image_of_injOn (ruzsaMark_injOn hp g), card_range]

theorem ruzsaRuler_lt {p : ℕ} (hp : 2 ≤ p) (g : ZMod p) :
    ∀ x ∈ ruzsaRuler p g, x < p * (p - 1) := by
  intro x hx
  simp only [ruzsaRuler, mem_image, mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ruzsaMark_lt hp g i

/-- Powers of a generator of `(ZMod p)ˣ` with exponents below `p - 1` are distinct. -/
theorem pow_inj_of_lt {p : ℕ} [Fact p.Prime] {g : (ZMod p)ˣ} (hg : orderOf g = p - 1)
    {i k : ℕ} (hi : i < p - 1) (hk : k < p - 1)
    (h : (g : ZMod p) ^ i = (g : ZMod p) ^ k) : i = k := by
  have h' : g ^ i = g ^ k := Units.ext (by simpa using h)
  exact pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hg]; exact hi)
    (by rw [Set.mem_Iio, hg]; exact hk) h'

theorem ruzsaRuler_sidon {p : ℕ} [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1) :
    IsSidon (ruzsaRuler p g) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  intro a ha b hb c hc d hd habcd
  simp only [ruzsaRuler, mem_image, mem_range] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨l, hl, rfl⟩ := hd
  have hsum : i + j ≡ k + l [MOD p - 1] :=
    ((ruzsaMark_modEq hp2 g hi).add (ruzsaMark_modEq hp2 g hj)).symm.trans
      (habcd ▸ (ruzsaMark_modEq hp2 g hk).add (ruzsaMark_modEq hp2 g hl))
  have hpow : g ^ (i + j) = g ^ (k + l) := by
    rw [pow_eq_pow_iff_modEq, hg]; exact hsum
  have hprod : (g : ZMod p) ^ i * (g : ZMod p) ^ j = (g : ZMod p) ^ k * (g : ZMod p) ^ l := by
    have := congrArg Units.val hpow
    simpa [pow_add] using this
  have hcast := congrArg (fun n : ℕ => (n : ZMod p)) habcd
  simp only [Nat.cast_add, ruzsaMark_cast] at hcast
  have hsumZ : (g : ZMod p) ^ i + (g : ZMod p) ^ j = (g : ZMod p) ^ k + (g : ZMod p) ^ l := by
    linear_combination -hcast
  have hz : ((g : ZMod p) ^ i - (g : ZMod p) ^ k) * ((g : ZMod p) ^ i - (g : ZMod p) ^ l) = 0 := by
    linear_combination (g : ZMod p) ^ i * hsumZ - hprod
  rcases mul_eq_zero.mp hz with h | h
  · have hik : (g : ZMod p) ^ i = (g : ZMod p) ^ k := sub_eq_zero.mp h
    have hjl : (g : ZMod p) ^ j = (g : ZMod p) ^ l := by
      linear_combination hsumZ - hik
    have e1 := pow_inj_of_lt hg hi hk hik
    have e2 := pow_inj_of_lt hg hj hl hjl
    subst e1; subst e2
    exact Or.inl ⟨rfl, rfl⟩
  · have hil : (g : ZMod p) ^ i = (g : ZMod p) ^ l := sub_eq_zero.mp h
    have hjk : (g : ZMod p) ^ j = (g : ZMod p) ^ k := by
      linear_combination hsumZ - hil
    have e1 := pow_inj_of_lt hg hi hl hil
    have e2 := pow_inj_of_lt hg hj hk hjk
    subst e1; subst e2
    exact Or.inr ⟨rfl, rfl⟩

/-- Ruzsa's bound: a prime `p > m` gives `f m ≤ p(p-1) - 1`. -/
theorem f_le_ruzsa {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hmp : m < p) :
    f m ≤ p * (p - 1) - 1 := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  exact f_le_of_sidon hm (ruzsaRuler p g) (ruzsaRuler_sidon g hord)
    (by rw [ruzsaRuler_card hp.two_le]; omega) (ruzsaRuler_lt hp.two_le g)

theorem ruzsaLen_valid : UpperBoundHolds f ruzsaLen := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [f, nMin]
  · obtain ⟨hp, hlt⟩ := SqueezeBench.Golomb.Upper.V002.nextPrime_spec hm
    exact f_le_ruzsa hp hm hlt

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Golomb.Upper.V005.valid ruzsaLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V005.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V005.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 18) (by decide)
    (by decide +kernel)

end SqueezeBench.Golomb.Upper.V006
