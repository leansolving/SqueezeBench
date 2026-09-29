import SqueezeBench.Problems.CapSet.Records.Lower.V002.Def
import SqueezeBench.Problems.CapSet.Records.Lower.V001.Proof

/-! Record V002 for CapSet, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Lower/V002.lean`. -/

namespace SqueezeBench.CapSet.Lower.V002

open SqueezeBench SqueezeBench.CapSet Finset

-- A cap of size 45 in `F₃^5`, found by tabu search; 45 is the exact value of `f 5`.
def pts : List (Fin 5 → ZMod 3) :=
  [
    ![2,1,2,2,1], ![2,1,0,0,2], ![0,0,0,0,0], ![2,0,1,2,2], ![1,2,1,0,2], ![0,1,2,1,1], 
    ![2,1,0,1,2], ![1,1,2,1,0], ![1,0,2,1,2], ![0,0,2,1,0], ![1,1,1,1,1], ![1,2,0,1,2], 
    ![1,0,0,1,2], ![0,1,0,0,0], ![2,0,1,0,1], ![1,2,0,1,1], ![2,2,0,1,0], ![2,0,1,0,0], 
    ![0,0,1,1,1], ![2,2,1,0,0], ![0,1,0,2,2], ![0,2,2,1,1], ![2,2,0,0,0], ![0,2,0,1,0], 
    ![1,2,2,2,1], ![0,2,0,0,2], ![0,0,2,0,1], ![2,0,2,0,0], ![2,1,0,1,0], ![1,0,1,0,1], 
    ![1,1,1,2,1], ![0,2,2,1,0], ![2,2,2,1,1], ![1,1,2,1,1], ![0,2,2,0,2], ![0,1,0,0,2], 
    ![1,0,2,2,1], ![2,0,2,2,2], ![0,1,0,1,0], ![2,2,0,0,1], ![2,1,0,2,0], ![1,2,0,0,2], 
    ![0,0,2,0,0], ![1,1,2,0,2], ![1,0,2,2,2]
  ]

def cap : Finset (Fin 5 → ZMod 3) := pts.toFinset

-- Base-3 code of a point, a number below 3^5.
def enc (v : Fin 5 → ZMod 3) : ℕ := (v 0).val + 3 * ((v 1).val + 3 * ((v 2).val + 3 * ((v 3).val + 3 * ((v 4).val))))

-- Bit `enc v` of `mask` is set exactly on the points of `pts`; a shift is an O(1) oracle
-- for membership, so three-AP freeness costs pairs rather than triples.
def mask : ℕ :=
  165858434806147458098853429060651106058473323770096511570966979800336649

def mem (v : Fin 5 → ZMod 3) : Bool := (mask >>> enc v) % 2 == 1

theorem pts_mem : ∀ v ∈ pts, mem v = true := by decide +kernel

-- The pair test: no two points of the cap have their third collinear point in the mask.
theorem pts_pair : ∀ x ∈ pts, ∀ y ∈ pts, x = y ∨ mem (y + y - x) = false := by decide +kernel

theorem cap_free : ThreeAPFree (cap : Set (Fin 5 → ZMod 3)) := by
  intro x hx y hy z hz hxyz
  have hx' : x ∈ pts := by simpa [cap] using hx
  have hy' : y ∈ pts := by simpa [cap] using hy
  have hz' : z ∈ pts := by simpa [cap] using hz
  have hzz : y + y - x = z := by rw [← hxyz]; abel
  rcases pts_pair x hx' y hy' with h | h
  · exact h
  · rw [hzz] at h
    rw [pts_mem z hz'] at h
    exact absurd h (by simp)

theorem cap_card : cap.card = 45 := by decide +kernel

theorem f5 : 45 ≤ SqueezeBench.CapSet.f 5 := by
  have h := SqueezeBench.CapSet.le_f_of_threeAPFree (A := cap) (by decide) cap_free
  rwa [cap_card] at h

theorem key : ∀ n, 1 ≤ n → 45 ^ (n / 5) * head (n % 5) ≤ SqueezeBench.CapSet.f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hbig : 6 ≤ n
    · have hm : 1 ≤ n - 5 := by omega
      have hdiv : n / 5 = (n - 5) / 5 + 1 := by omega
      have hmod : n % 5 = (n - 5) % 5 := by omega
      have hrec := ih (n - 5) (by omega) hm
      calc 45 ^ (n / 5) * head (n % 5)
          = 45 * (45 ^ ((n - 5) / 5) * head ((n - 5) % 5)) := by
            rw [hdiv, hmod]; ring
        _ ≤ SqueezeBench.CapSet.f 5 * SqueezeBench.CapSet.f (n - 5) := Nat.mul_le_mul f5 hrec
        _ ≤ SqueezeBench.CapSet.f (5 + (n - 5)) :=
            SqueezeBench.CapSet.Lower.V001.f_mul_le 5 (n - 5) (by norm_num) hm
        _ = SqueezeBench.CapSet.f n := by rw [show 5 + (n - 5) = n from by omega]
    · interval_cases n
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f1
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f2
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f3
      · simpa [head] using SqueezeBench.CapSet.Lower.V001.f4
      · simpa [head] using f5

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f blocks :=
  SqueezeBench.pin_lowerBoundHolds fun n hn => key n (by simpa using hn)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.CapSet.Lower.V001.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.CapSet.Lower.V001.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Lower.V001.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.CapSet.nMin) (n₀ := 5) (by decide) (by decide)

end SqueezeBench.CapSet.Lower.V002
