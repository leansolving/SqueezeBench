import SqueezeBench.Problems.Golomb.Records.Upper.V001.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V000.Proof

/-!
# Golomb upper-bound record V001 — validity

The Erdős–Turán construction. For a prime `p` and `k < p`, put `aₖ = 2pk + (k² mod p)`.
Since the residues are `< p`, a sum `aᵢ + aⱼ` splits uniquely as `2p(i+j)` plus a remainder
`< 2p`, so `aᵢ + aⱼ = a_k + a_l` forces `i + j = k + l` over `ℕ` and
`i² + j² ≡ k² + l² (mod p)`. In the field `ZMod p` with `p` odd this gives `ij = kl`, hence
`(i - k)(i - l) = 0` and `{i, j} = {k, l}`.

Only the first `m` marks are used, so the length is `2p(m-1) + ((m-1)² mod p)`. Bertrand's
postulate supplies a prime `m < p ≤ 2m`, and the length is then at most
`2·2m·(m-1) + (2m - 1) = 4m² - 2m - 1`.

`div_unique` is reused from V000.
-/

namespace SqueezeBench.Golomb.Upper.V001

open SqueezeBench Finset

/-- Marks with distinct indices are ordered by their index, because residues are `< p`. -/
theorem mark_lt {p i j ri rj : ℕ} (hri : ri < p) (h : i < j) :
    2 * p * i + ri < 2 * p * j + rj := by
  calc 2 * p * i + ri < 2 * p * i + 2 * p := Nat.add_lt_add_left (by omega) _
    _ = 2 * p * (i + 1) := by ring
    _ ≤ 2 * p * j := Nat.mul_le_mul_left _ h
    _ ≤ 2 * p * j + rj := Nat.le_add_right _ _

/-- The Erdős–Turán ruler modulo `p`, truncated to its first `m` marks. -/
def etRuler (p m : ℕ) : Finset ℕ := (range m).image (fun k => 2 * p * k + k ^ 2 % p)

theorem etRuler_card {p m : ℕ} (hp : 0 < p) : (etRuler p m).card = m := by
  rw [etRuler, card_image_of_injective _ ?_, card_range]
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (Nat.ne_of_lt (mark_lt (Nat.mod_lt _ hp) h))
  · exact h
  · exact absurd hij.symm (Nat.ne_of_lt (mark_lt (Nat.mod_lt _ hp) h))

/-- Nat casts are injective below the modulus. -/
theorem cast_inj_of_lt {p a b : ℕ} (hp : 0 < p) (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hv

theorem etRuler_sidon {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmp : m ≤ p) :
    IsSidon (etRuler p m) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hppos : 0 < p := hp.pos
  have htwo : (2 : ZMod p) ≠ 0 := by
    have h2n : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    simpa using h2n
  intro a ha b hb c hc d hd habcd
  simp only [etRuler, mem_image, mem_range] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨l, hl, rfl⟩ := hd
  have e1 : 2 * p * i + i ^ 2 % p + (2 * p * j + j ^ 2 % p)
      = 2 * p * (i + j) + (i ^ 2 % p + j ^ 2 % p) := by ring
  have e2 : 2 * p * k + k ^ 2 % p + (2 * p * l + l ^ 2 % p)
      = 2 * p * (k + l) + (k ^ 2 % p + l ^ 2 % p) := by ring
  have hgroup : 2 * p * (i + j) + (i ^ 2 % p + j ^ 2 % p)
      = 2 * p * (k + l) + (k ^ 2 % p + l ^ 2 % p) := by rw [← e1, ← e2]; exact habcd
  have hb1 : i ^ 2 % p + j ^ 2 % p < 2 * p := by
    have h1 := Nat.mod_lt (i ^ 2) hppos
    have h2 := Nat.mod_lt (j ^ 2) hppos
    omega
  have hb2 : k ^ 2 % p + l ^ 2 % p < 2 * p := by
    have h1 := Nat.mod_lt (k ^ 2) hppos
    have h2 := Nat.mod_lt (l ^ 2) hppos
    omega
  obtain ⟨hsum, hres⟩ := V000.div_unique hb1 hb2 hgroup
  have hI : (i : ZMod p) + (j : ZMod p) = (k : ZMod p) + (l : ZMod p) := by
    have h : ((i + j : ℕ) : ZMod p) = ((k + l : ℕ) : ZMod p) := by rw [hsum]
    push_cast at h
    exact h
  have hQ : (i : ZMod p) ^ 2 + (j : ZMod p) ^ 2 = (k : ZMod p) ^ 2 + (l : ZMod p) ^ 2 := by
    have h : ((i ^ 2 % p + j ^ 2 % p : ℕ) : ZMod p) = ((k ^ 2 % p + l ^ 2 % p : ℕ) : ZMod p) := by
      rw [hres]
    push_cast [ZMod.natCast_mod] at h
    exact h
  have hP : (i : ZMod p) * (j : ZMod p) = (k : ZMod p) * (l : ZMod p) := by
    refine mul_left_cancel₀ htwo ?_
    linear_combination ((i : ZMod p) + (j : ZMod p) + (k : ZMod p) + (l : ZMod p)) * hI - hQ
  have hz : ((i : ZMod p) - (k : ZMod p)) * ((i : ZMod p) - (l : ZMod p)) = 0 := by
    linear_combination (i : ZMod p) * hI - hP
  have hip : i < p := lt_of_lt_of_le hi hmp
  have hkp : k < p := lt_of_lt_of_le hk hmp
  have hlp : l < p := lt_of_lt_of_le hl hmp
  rcases mul_eq_zero.mp hz with h | h
  · have hik : i = k := cast_inj_of_lt hppos hip hkp (sub_eq_zero.mp h)
    left
    exact ⟨by rw [hik], by rw [show j = l by omega]⟩
  · have hil : i = l := cast_inj_of_lt hppos hip hlp (sub_eq_zero.mp h)
    right
    exact ⟨by rw [hil], by rw [show j = k by omega]⟩

/-- The length of the truncated ruler is achievable. -/
theorem etRuler_mem {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (hmp : m ≤ p) :
    2 * p * (m - 1) + (m - 1) ^ 2 % p ∈ RulerLengths m := by
  have hppos : 0 < p := hp.pos
  refine ⟨etRuler p m, ?_, etRuler_card hppos, etRuler_sidon hp hp2 hmp, ?_⟩
  · intro x hx
    simp only [etRuler, mem_image, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_range]
    rcases Nat.lt_or_ge i (m - 1) with h | h
    · exact Nat.lt_succ_of_lt (mark_lt (Nat.mod_lt _ hppos) h)
    · have hieq : i = m - 1 := by omega
      subst hieq
      exact Nat.lt_succ_self _
  · simp only [etRuler, mem_image, mem_range]
    exact ⟨m - 1, by omega, rfl⟩

theorem etLen_valid : UpperBoundHolds f etLen := by
  intro m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [f, nMin]
    · exact le_trans (f_le_binRuler 1 (by simp)) (by norm_num [etLen])
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (t + 2) (by omega)
    have hp2 : p ≠ 2 := by omega
    have hmem := etRuler_mem hp hp2 (by omega) (le_of_lt hlt)
    have hf : f (t + 2) ≤ 2 * p * (t + 2 - 1) + (t + 2 - 1) ^ 2 % p :=
      f_le_of_mem (by simp) hmem
    have hs : t + 2 - 1 = t + 1 := by omega
    rw [hs] at hf
    have hr : (t + 1) ^ 2 % p < p := Nat.mod_lt _ hp.pos
    have hpb : p ≤ 2 * t + 4 := by omega
    have hexp : 4 * (t + 2) ^ 2 = 4 * t ^ 2 + 16 * t + 16 := by ring
    have hgoal : etLen (t + 2) = 4 * t ^ 2 + 14 * t + 11 := by
      simp only [etLen]; omega
    rw [hgoal]
    refine le_trans hf ?_
    have hmul : p * (t + 1) ≤ (2 * t + 4) * (t + 1) := Nat.mul_le_mul_right (t + 1) hpb
    nlinarith [hr, hmul, hpb]

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  minWith_valid V000.valid etLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V000.record record :=
  minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V000.record record :=
  minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 10) (by decide) (by decide)

end SqueezeBench.Golomb.Upper.V001
