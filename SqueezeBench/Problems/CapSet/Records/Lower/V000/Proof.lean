import SqueezeBench.Problems.CapSet.Records.Lower.V000.Def

/-!
# CapSet lower-bound record V000 — validity
-/

namespace SqueezeBench.CapSet.Lower.V000

open SqueezeBench Finset

def boolCap (n : ℕ) : Finset (Fin n → ZMod 3) :=
  Fintype.piFinset (fun _ => ({0, 1} : Finset (ZMod 3)))

theorem boolCap_card (n : ℕ) : (boolCap n).card = 2 ^ n := by
  rw [boolCap, Fintype.card_piFinset_const]
  norm_num

theorem boolCap_threeAPFree (n : ℕ) :
    ThreeAPFree ((boolCap n : Finset (Fin n → ZMod 3)) : Set (Fin n → ZMod 3)) := by
  have key : ∀ x y z : ZMod 3, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → (z = 0 ∨ z = 1) →
      x + z = y + y → x = y := by decide
  intro a ha b hb c hc habc
  simp only [mem_coe, boolCap, Fintype.mem_piFinset, mem_insert, mem_singleton] at ha hb hc
  funext i
  have h := congrFun habc i
  simp only [Pi.add_apply] at h
  exact key (a i) (b i) (c i) (ha i) (hb i) (hc i) h

theorem valid : LowerBoundHolds f record :=
  pin_lowerBoundHolds fun n hn => by
    have := le_f_of_threeAPFree (A := boolCap n) hn (boolCap_threeAPFree n)
    rwa [boolCap_card] at this

end SqueezeBench.CapSet.Lower.V000
