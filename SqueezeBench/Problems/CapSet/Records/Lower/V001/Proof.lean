import SqueezeBench.Problems.CapSet.Records.Lower.V001.Def
import SqueezeBench.Problems.CapSet.Records.Lower.V000.Proof

/-! Record V001 for CapSet, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Lower/V001.lean`. -/

namespace SqueezeBench.CapSet.Lower.V001

open SqueezeBench SqueezeBench.CapSet Finset

-- Concatenating coordinates is additive, so a product of caps is a cap.
theorem append_add {m n : ℕ} (a b : Fin m → ZMod 3) (c d : Fin n → ZMod 3) :
    Fin.append a c + Fin.append b d = Fin.append (a + b) (c + d) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem f_eq {n : ℕ} (hn : 1 ≤ n) :
    SqueezeBench.CapSet.f n = addRothNumber (univ : Finset (Fin n → ZMod 3)) := by
  rw [SqueezeBench.CapSet.f, if_neg (Nat.not_lt.mpr (by simpa using hn))]

-- The product of a cap in `F₃ᵐ` and a cap in `F₃ⁿ` is a cap in `F₃^(m+n)`.
theorem f_mul_le (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    SqueezeBench.CapSet.f m * SqueezeBench.CapSet.f n ≤ SqueezeBench.CapSet.f (m + n) := by
  obtain ⟨A, -, hAcard, hA⟩ := addRothNumber_spec (univ : Finset (Fin m → ZMod 3))
  obtain ⟨B, -, hBcard, hB⟩ := addRothNumber_spec (univ : Finset (Fin n → ZMod 3))
  set g : (Fin m → ZMod 3) × (Fin n → ZMod 3) → (Fin (m + n) → ZMod 3) :=
    fun p => Fin.append p.1 p.2 with hg
  have hinj : Function.Injective g := (Fin.appendEquiv m n).injective
  have hcard : (Finset.image g (A ×ˢ B)).card = A.card * B.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product]
  have hfree : ThreeAPFree ((Finset.image g (A ×ˢ B) : Finset (Fin (m + n) → ZMod 3)) :
      Set (Fin (m + n) → ZMod 3)) := by
    intro x hx y hy z hz hxyz
    simp only [mem_coe, Finset.mem_image, Finset.mem_product] at hx hy hz
    obtain ⟨⟨x1, x2⟩, ⟨hx1, hx2⟩, rfl⟩ := hx
    obtain ⟨⟨y1, y2⟩, ⟨hy1, hy2⟩, rfl⟩ := hy
    obtain ⟨⟨z1, z2⟩, ⟨hz1, hz2⟩, rfl⟩ := hz
    rw [hg] at hxyz
    simp only [append_add] at hxyz
    have hxyz' : g (x1 + z1, x2 + z2) = g (y1 + y1, y2 + y2) := hxyz
    have hpair := hinj hxyz'
    simp only [Prod.mk.injEq] at hpair
    have e1 : x1 = y1 := hA hx1 hy1 hz1 hpair.1
    have e2 : x2 = y2 := hB hx2 hy2 hz2 hpair.2
    simp [hg, e1, e2]
  have hle := hfree.le_addRothNumber (subset_univ _)
  rw [hcard, hAcard, hBcard] at hle
  rw [f_eq hm, f_eq hn, f_eq (by omega : 1 ≤ m + n)]
  exact hle

-- A cap of size 9 in `F₃³`, found by exhaustive search; 9 is the exact value of `f 3`.
def cap3 : Finset (Fin 3 → ZMod 3) :=
  ({![0,0,0], ![1,0,0], ![0,1,0], ![0,0,1], ![0,1,1], ![1,0,1], ![1,1,2], ![1,2,2],
    ![2,1,2]} : List (Fin 3 → ZMod 3)).toFinset

-- A cap of size 20 in `F₃⁴`, found by exhaustive search; 20 is the exact value of `f 4`.
def cap4 : Finset (Fin 4 → ZMod 3) :=
  ({![0,0,0,0], ![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1], ![0,0,1,1], ![0,1,0,1],
    ![0,1,1,0], ![0,1,1,1], ![1,0,0,1], ![1,0,1,2], ![1,0,2,2], ![1,1,0,2], ![1,2,0,2],
    ![2,0,1,2], ![2,1,0,2], ![2,1,1,0], ![2,1,1,1], ![2,1,2,2],
    ![2,2,1,2]} : List (Fin 4 → ZMod 3)).toFinset

theorem f3 : 9 ≤ SqueezeBench.CapSet.f 3 := by
  have h := SqueezeBench.CapSet.le_f_of_threeAPFree (A := cap3) (by decide) (by decide)
  rwa [show cap3.card = 9 from by decide] at h

theorem f4 : 20 ≤ SqueezeBench.CapSet.f 4 := by
  have h := SqueezeBench.CapSet.le_f_of_threeAPFree (A := cap4) (by decide) (by decide)
  rwa [show cap4.card = 20 from by decide] at h

theorem f1 : 2 ≤ SqueezeBench.CapSet.f 1 := by
  have h := SqueezeBench.CapSet.Lower.V000.valid 1
  simpa [SqueezeBench.CapSet.Lower.V000.record, SqueezeBench.pin] using h

theorem f2 : 4 ≤ SqueezeBench.CapSet.f 2 := by
  have h := SqueezeBench.CapSet.Lower.V000.valid 2
  simpa [SqueezeBench.CapSet.Lower.V000.record, SqueezeBench.pin] using h

theorem key : ∀ n, 1 ≤ n → 20 ^ (n / 4) * head (n % 4) ≤ SqueezeBench.CapSet.f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h5 : 5 ≤ n
    · have hm : 1 ≤ n - 4 := by omega
      have hdiv : n / 4 = (n - 4) / 4 + 1 := by omega
      have hmod : n % 4 = (n - 4) % 4 := by omega
      have hrec := ih (n - 4) (by omega) hm
      calc 20 ^ (n / 4) * head (n % 4)
          = 20 * (20 ^ ((n - 4) / 4) * head ((n - 4) % 4)) := by rw [hdiv, hmod]; ring
        _ ≤ SqueezeBench.CapSet.f 4 * SqueezeBench.CapSet.f (n - 4) := Nat.mul_le_mul f4 hrec
        _ ≤ SqueezeBench.CapSet.f (4 + (n - 4)) := f_mul_le 4 (n - 4) (by norm_num) hm
        _ = SqueezeBench.CapSet.f n := by rw [show 4 + (n - 4) = n from by omega]
    · interval_cases n
      · simpa [head] using f1
      · simpa [head] using f2
      · simpa [head] using f3
      · simpa [head] using f4

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f blocks :=
  SqueezeBench.pin_lowerBoundHolds fun n hn => key n (by simpa using hn)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.CapSet.Lower.V000.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.CapSet.Lower.V000.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Lower.V000.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.CapSet.nMin) (n₀ := 4) (by decide) (by decide)

end SqueezeBench.CapSet.Lower.V001
