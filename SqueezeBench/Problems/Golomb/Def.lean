import Mathlib
import SqueezeBench.Core

/-!
# Optimal Golomb rulers

An `m`-mark Golomb ruler is a set of `m` integers whose pairwise differences are all
distinct; equivalently a Sidon (B₂) set. `f m` is the least possible length — the largest
mark, with marks normalised to start at `0`. See OEIS A003022.

`f` is defined by `sInf`, so it is meaningful only once `RulerLengths m` is known to be
nonempty. That is `rulerLengths_nonempty`, proved below via the binary ruler
`{0, 1, 3, 7, …, 2^(m-1) - 1}`.
-/

namespace SqueezeBench.Golomb

open Finset

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- A Sidon (B₂) set: a pairwise sum determines the unordered pair it came from.

For a finite set of integers this is equivalent to all **positive** pairwise differences
being distinct — the standard Golomb-ruler condition. The qualifier matters: the *signed*
differences are never all distinct, since `a - b` and `b - a` always both occur. Working
with sums avoids the issue entirely and is also OEIS A003022's own phrasing. -/
def IsSidon (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance (S : Finset ℕ) : Decidable (IsSidon S) :=
  inferInstanceAs (Decidable
    (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)))

/-- Lengths achievable by an `m`-mark Golomb ruler laid out on `{0, …, L}` with a mark
at `L`. -/
def RulerLengths (m : ℕ) : Set ℕ :=
  {L | ∃ S : Finset ℕ, S ⊆ range (L + 1) ∧ S.card = m ∧ IsSidon S ∧ L ∈ S}

/-! ## The binary ruler

`{0, 1, 3, 7, …, 2^(m-1) - 1}` is a Sidon set of size `m`, by uniqueness of binary
representations. The length it achieves is exponential in `m`, but it suffices to make
`f` well posed. -/

/-- Uniqueness of binary representations, in the form needed for the Sidon property. -/
theorem pow2_sidon : ∀ i j k l : ℕ, 2 ^ i + 2 ^ j = 2 ^ k + 2 ^ l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have pos : ∀ n : ℕ, 1 ≤ 2 ^ n := fun n => Nat.one_le_two_pow
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j k l h
    match i, j, k, l with
    | 0, 0, 0, 0 => simp
    | 0, 0, 0, l + 1 => exfalso; have := pos l; simp [pow_succ] at h; omega
    | 0, 0, k + 1, l => exfalso; have := pos k; have := pos l; simp [pow_succ] at h; omega
    | 0, j + 1, 0, 0 => exfalso; have := pos j; simp [pow_succ] at h; omega
    | 0, j + 1, 0, l + 1 =>
      have : 2 ^ (j + 1) = 2 ^ (l + 1) := by omega
      have := Nat.pow_right_injective (le_refl 2) this
      omega
    | 0, j + 1, k + 1, l =>
      match l with
      | 0 =>
        have : 2 ^ (j + 1) = 2 ^ (k + 1) := by omega
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      | l + 1 => exfalso; simp [pow_succ] at h; omega
    | i + 1, j, 0, 0 => exfalso; have := pos i; have := pos j; simp [pow_succ] at h; omega
    | i + 1, j, 0, l + 1 =>
      match j with
      | 0 =>
        have : 2 ^ (i + 1) = 2 ^ (l + 1) := by omega
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      | j + 1 => exfalso; simp [pow_succ] at h; omega
    | i + 1, j, k + 1, l =>
      match j, l with
      | 0, 0 =>
        have : 2 ^ (i + 1) = 2 ^ (k + 1) := by omega
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      | 0, l + 1 => exfalso; simp [pow_succ] at h; omega
      | j + 1, 0 => exfalso; simp [pow_succ] at h; omega
      | j + 1, l + 1 =>
        have h' : 2 ^ i + 2 ^ j = 2 ^ k + 2 ^ l := by
          have : 2 * (2 ^ i + 2 ^ j) = 2 * (2 ^ k + 2 ^ l) := by
            ring_nf; ring_nf at h; omega
          omega
        rcases ih i (by omega) j k l h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; omega
        · right; omega

/-- The binary ruler `{0, 1, 3, 7, …, 2^(m-1) - 1}`. -/
def binRuler (m : ℕ) : Finset ℕ := (range m).image (fun i => 2 ^ i - 1)

theorem binRuler_card (m : ℕ) : (binRuler m).card = m := by
  unfold binRuler
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a _ b _ h
  simp only at h
  have ha := Nat.one_le_two_pow (n := a)
  have hb := Nat.one_le_two_pow (n := b)
  have : (2 : ℕ) ^ a = 2 ^ b := by omega
  exact Nat.pow_right_injective (le_refl 2) this

theorem binRuler_sidon (m : ℕ) : IsSidon (binRuler m) := by
  intro a ha b hb c hc d hd habcd
  simp only [binRuler, Finset.mem_image, Finset.mem_range] at ha hb hc hd
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hb
  obtain ⟨k, _, rfl⟩ := hc
  obtain ⟨l, _, rfl⟩ := hd
  have p : ∀ n : ℕ, 1 ≤ 2 ^ n := fun n => Nat.one_le_two_pow
  have := p i; have := p j; have := p k; have := p l
  have key : 2 ^ i + 2 ^ j = 2 ^ k + 2 ^ l := by omega
  rcases pow2_sidon i j k l key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
  · right; subst h1; subst h2; exact ⟨rfl, rfl⟩

theorem binRuler_subset (m : ℕ) : binRuler m ⊆ range (2 ^ (m - 1) - 1 + 1) := by
  intro x hx
  simp only [binRuler, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [Finset.mem_range]
  have : (2 : ℕ) ^ i ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.one_le_two_pow (n := i)
  omega

theorem binRuler_max (m : ℕ) (hm : nMin ≤ m) : 2 ^ (m - 1) - 1 ∈ binRuler m := by
  simp only [binRuler, Finset.mem_image, Finset.mem_range]
  exact ⟨m - 1, by simp only [nMin_eq] at hm; omega, rfl⟩

/-- Well-posedness: `RulerLengths m` is nonempty, so `sInf` of it is a genuine minimum. -/
theorem rulerLengths_nonempty (m : ℕ) (hm : nMin ≤ m) : (RulerLengths m).Nonempty :=
  ⟨2 ^ (m - 1) - 1, binRuler m, binRuler_subset m, binRuler_card m, binRuler_sidon m,
    binRuler_max m hm⟩

/-- The obligation that makes `f` meaningful, named uniformly with the other problems. -/
def WellPosed (m : ℕ) : Prop := (RulerLengths m).Nonempty

theorem wellPosed (m : ℕ) (hm : nMin ≤ m) : WellPosed m := rulerLengths_nonempty m hm

/-! ## The target function -/

/-- The least length of an `m`-mark Golomb ruler, pinned to `0` below `nMin`. -/
noncomputable def f (m : ℕ) : ℕ := if m < nMin then 0 else sInf (RulerLengths m)

/-- Above `nMin`, upper bounds on `f` reduce to exhibiting a ruler. -/
theorem f_le_of_mem {m L : ℕ} (hm : nMin ≤ m) (hL : L ∈ RulerLengths m) : f m ≤ L := by
  rw [f, if_neg (Nat.not_lt.mpr hm)]
  exact Nat.sInf_le hL

/-- Lower bounds on `f` reduce to a lower bound on every achievable length.
Unconditional, because well-posedness is proved. -/
theorem le_f {m a : ℕ} (hm : nMin ≤ m) (h : ∀ L ∈ RulerLengths m, a ≤ L) : a ≤ f m := by
  rw [f, if_neg (Nat.not_lt.mpr hm)]
  exact h _ (Nat.sInf_mem (rulerLengths_nonempty m hm))

/-- The binary ruler as an upper bound on `f`, from the same witness as
`rulerLengths_nonempty`. -/
theorem f_le_binRuler (m : ℕ) (hm : nMin ≤ m) : f m ≤ 2 ^ (m - 1) - 1 :=
  f_le_of_mem hm ⟨binRuler m, binRuler_subset m, binRuler_card m, binRuler_sidon m,
    binRuler_max m hm⟩

end SqueezeBench.Golomb
