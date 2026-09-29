import SqueezeBench.Problems.Golomb.Records.Upper.V008.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V007.Proof

-- Golomb upper-bound record V008 — validity.
-- `SidonMod n S`: a pairwise sum modulo `n` determines the unordered pair. `window_exists` is
-- the double count: the pairs `(x, j)` with `x ∈ S`, `j ≤ L` map to the rotation `t ≡ j - x`,
-- so if `(m-1) n < |S| (L+1)` some `t < n` has at least `m` residues `x` with `(x+t) mod n ≤ L`
-- (Mathlib's `exists_lt_card_fiber_of_mul_lt_card_of_maps_to`). `f_le_of_sidonMod` rotates `S`
-- by that `t`: the residues in the window are a Sidon set of naturals below `L + 1`, since an
-- equality of sums of rotated residues is a congruence of the original sums modulo `n`, and
-- V006's `f_le_of_sidon` finishes. `ruzsaRuler_sidonMod` is V006's Sidon proof with the
-- integer equality replaced by a congruence modulo `p(p-1)`, which reduces modulo `p - 1` and
-- modulo `p` exactly as before. The window `L = (m-1) p` works since `p(p-1)/(p-1) = p`.

namespace SqueezeBench.Golomb.Upper.V008

open SqueezeBench Finset
open SqueezeBench.Golomb.Upper.V006 (f_le_of_sidon ruzsaMark ruzsaRuler ruzsaMark_lt ruzsaMark_modEq
  ruzsaMark_cast ruzsaRuler_card ruzsaRuler_lt pow_inj_of_lt)

/-- Sidon modulo `n`: a pairwise sum modulo `n` determines the unordered pair. -/
def SidonMod (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    (a + b) % n = (c + d) % n → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Some rotation of `S` puts at least `m` of its residues into the window `[0, L]`. -/
theorem window_exists {n L m : ℕ} (hn : 0 < n) (S : Finset ℕ) (hS : ∀ x ∈ S, x < n)
    (hLn : L < n) (hcount : (m - 1) * n < S.card * (L + 1)) :
    ∃ t < n, m ≤ (S.filter (fun x => (x + t) % n ≤ L)).card := by
  have hcard : (S ×ˢ range (L + 1)).card = S.card * (L + 1) := by
    rw [card_product, card_range]
  obtain ⟨t, ht, hfib⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S ×ˢ range (L + 1)) (t := range n) (f := fun q : ℕ × ℕ => (q.2 + n - q.1) % n)
    (n := m - 1) (fun q _ => mem_range.mpr (Nat.mod_lt _ hn))
    (by rw [card_range, hcard, mul_comm n]; exact hcount)
  refine ⟨t, mem_range.mp ht, ?_⟩
  have hmaps : ∀ q ∈ (S ×ˢ range (L + 1)).filter (fun q : ℕ × ℕ => (q.2 + n - q.1) % n = t),
      q.1 ∈ S.filter (fun x => (x + t) % n ≤ L) := by
    intro q hq
    rw [mem_filter, mem_product, mem_range] at hq
    obtain ⟨⟨hx, hj⟩, hqt⟩ := hq
    rw [mem_filter]
    refine ⟨hx, ?_⟩
    have hxn := hS _ hx
    rw [← hqt, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show q.1 + (q.2 + n - q.1) = q.2 + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  have hinj : Set.InjOn Prod.fst
      (↑((S ×ˢ range (L + 1)).filter (fun q : ℕ × ℕ => (q.2 + n - q.1) % n = t)) : Set (ℕ × ℕ)) := by
    intro q hq q' hq' heq
    rw [coe_filter, Set.mem_setOf_eq, mem_product, mem_range] at hq hq'
    obtain ⟨⟨hx, hj⟩, hqt⟩ := hq
    obtain ⟨⟨hx', hj'⟩, hqt'⟩ := hq'
    have hxn := hS _ hx
    have hmod : (q.2 + (n - q.1)) % n = (q'.2 + (n - q.1)) % n := by
      rw [← Nat.add_sub_assoc (by omega), ← Nat.add_sub_assoc (by omega), hqt, heq, hqt']
    have := Nat.ModEq.add_right_cancel' (n - q.1) hmod
    have h2 : q.2 = q'.2 := Nat.ModEq.eq_of_lt_of_lt this (by omega) (by omega)
    exact Prod.ext heq h2
  have h1 := card_le_card_of_injOn Prod.fst hmaps hinj
  omega

/-- A Sidon set modulo `n` with `k` residues yields `f m ≤ L` whenever `(m-1) n < k (L+1)`. -/
theorem f_le_of_sidonMod {n m L : ℕ} (hn : 0 < n) (S : Finset ℕ) (hS : ∀ x ∈ S, x < n)
    (hsid : SidonMod n S) (hm : 1 ≤ m) (hLn : L < n)
    (hcount : (m - 1) * n < S.card * (L + 1)) : f m ≤ L := by
  obtain ⟨t, htn, hcard⟩ := window_exists hn S hS hLn hcount
  have hrot : ∀ x ∈ S, ∀ y ∈ S, (x + t) % n = (y + t) % n → x = y := by
    intro x hx y hy h
    have := Nat.ModEq.add_right_cancel' t h
    exact Nat.ModEq.eq_of_lt_of_lt this (hS x hx) (hS y hy)
  refine le_trans (f_le_of_sidon (N := L + 1) hm ((S.filter (fun x => (x + t) % n ≤ L)).image
    (fun x => (x + t) % n)) ?_ ?_ ?_) (by omega)
  · intro a ha b hb c hc d hd habcd
    simp only [mem_image, mem_filter] at ha hb hc hd
    obtain ⟨a, ⟨ha, _⟩, rfl⟩ := ha
    obtain ⟨b, ⟨hb, _⟩, rfl⟩ := hb
    obtain ⟨c, ⟨hc, _⟩, rfl⟩ := hc
    obtain ⟨d, ⟨hd, _⟩, rfl⟩ := hd
    have h1 : (a + b + 2 * t) % n = (c + d + 2 * t) % n := by
      rw [show a + b + 2 * t = (a + t) + (b + t) by ring, show c + d + 2 * t = (c + t) + (d + t) by ring,
        Nat.add_mod, habcd, ← Nat.add_mod]
    have h2 := Nat.ModEq.add_right_cancel' (2 * t) h1
    rcases hsid a ha b hb c hc d hd h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rw [card_image_of_injOn]
    · exact hcard
    · intro x hx y hy h
      rw [coe_filter, Set.mem_setOf_eq] at hx hy
      exact hrot x hx.1 y hy.1 h
  · intro y hy
    simp only [mem_image, mem_filter] at hy
    obtain ⟨x, ⟨_, hxL⟩, rfl⟩ := hy
    omega

theorem ruzsaRuler_sidonMod {p : ℕ} [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1) :
    SidonMod (p * (p - 1)) (ruzsaRuler p g) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  intro a ha b hb c hc d hd habcd
  simp only [ruzsaRuler, mem_image, mem_range] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨l, hl, rfl⟩ := hd
  have hmod1 : ruzsaMark p g i + ruzsaMark p g j ≡ ruzsaMark p g k + ruzsaMark p g l [MOD p - 1] :=
    Nat.ModEq.of_mul_left p habcd
  have hmodp : ruzsaMark p g i + ruzsaMark p g j ≡ ruzsaMark p g k + ruzsaMark p g l [MOD p] :=
    Nat.ModEq.of_mul_right (p - 1) habcd
  have hsum : i + j ≡ k + l [MOD p - 1] :=
    ((ruzsaMark_modEq hp2 g hi).add (ruzsaMark_modEq hp2 g hj)).symm.trans
      (hmod1.trans ((ruzsaMark_modEq hp2 g hk).add (ruzsaMark_modEq hp2 g hl)))
  have hpow : g ^ (i + j) = g ^ (k + l) := by
    rw [pow_eq_pow_iff_modEq, hg]; exact hsum
  have hprod : (g : ZMod p) ^ i * (g : ZMod p) ^ j = (g : ZMod p) ^ k * (g : ZMod p) ^ l := by
    have := congrArg Units.val hpow
    simpa [pow_add] using this
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodp
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

/-- Ruzsa's ruler rotated into a window: a prime `p > m` gives `f m ≤ (m-1) p`. -/
theorem f_le_ruzsa_window {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hmp : m < p) :
    f m ≤ (m - 1) * p := by
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  refine f_le_of_sidonMod (Nat.mul_pos (by omega) (by omega)) (ruzsaRuler p g)
    (ruzsaRuler_lt hp2 g) (ruzsaRuler_sidonMod g hord) hm ?_ ?_
  · have : (m - 1) * p < (p - 1) * p := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    linarith [Nat.mul_comm p (p - 1)]
  · rw [ruzsaRuler_card hp2 g]
    have : (p - 1) * ((m - 1) * p + 1) = (m - 1) * (p * (p - 1)) + (p - 1) := by ring
    omega

theorem winLen_valid : UpperBoundHolds f winLen := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [f, nMin]
  · obtain ⟨hp, hlt⟩ := SqueezeBench.Golomb.Upper.V002.nextPrime_spec hm
    exact f_le_ruzsa_window hp hm hlt

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Golomb.Upper.V007.valid winLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V007.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V007.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 29) (by decide)
    (by decide +kernel)

end SqueezeBench.Golomb.Upper.V008
