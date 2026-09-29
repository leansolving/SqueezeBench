import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V008.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V007.Proof

/-! Record V008 for RuzsaSzemeredi, lower direction, by trial claude-fable: the three obligations.
Each table entry `zt N` is carried by an explicit list of residues that the kernel checks to be
3-AP-free in `Z_N`: for two distinct listed residues `a, b` the residue `2b - a` is not listed
(a bitmask lookup, `V007.CapCode.mask`), so `#L²` cheap steps per entry and no search.
`threeAPFree_cyc` turns that check into `ThreeAPFree` of the cast set in `Fin N`. V007's `trip`
is re-run with the Roth number of `Fin (2m+1)` in place of `rothNumberNat m`, and the choice of
the odd `N` is a `max` over valid terms. Reused verbatim from V007: `rs_of_ring`, the product
and pi lemmas, `TG`, `capr_le`, `C112_le`, `capB`, `log3` and the `CapCode` bitmask. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V008

open SqueezeBench Finset V007.CapCode

/-! ### Explicit 3-AP-free subsets of `Z_N` -/

/-- For distinct listed residues `a, b < N`, the residue `2b - a` is not listed. -/
def CycOk (M N a b : ℕ) : Prop := a = b ∨ M.testBit ((2 * b + N - a) % N) = false

instance (M N : ℕ) : DecidableRel (CycOk M N) :=
  fun a b => inferInstanceAs (Decidable (a = b ∨ M.testBit ((2 * b + N - a) % N) = false))

/-- The residue class of `a` in `Fin N`. -/
def res (N : ℕ) [NeZero N] (a : ℕ) : Fin N := ⟨a % N, Nat.mod_lt _ (NeZero.pos N)⟩

theorem val_res (N : ℕ) [NeZero N] (a : ℕ) : (res N a).val = a % N := rfl

/-- The residues of a list, as a finset of `Fin N`. -/
def cyc (N : ℕ) [NeZero N] (L : List ℕ) : Finset (Fin N) := (L.map (res N)).toFinset

theorem mem_cyc {N : ℕ} [NeZero N] {L : List ℕ} {x : Fin N} :
    x ∈ cyc N L ↔ ∃ a ∈ L, res N a = x := by
  simp [cyc]

theorem threeAPFree_cyc (N : ℕ) [NeZero N] (L : List ℕ) (hlt : ∀ a ∈ L, a < N)
    (hchk : ∀ a ∈ L, ∀ b ∈ L, CycOk (mask L) N a b) :
    ThreeAPFree (cyc N L : Set (Fin N)) := by
  intro x hx y hy z hz hxz
  rw [Finset.mem_coe, mem_cyc] at hx hy hz
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hz
  have hv := congrArg Fin.val hxz
  simp only [Fin.val_add, val_res, Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb),
    Nat.mod_eq_of_lt (hlt c hc)] at hv
  by_contra hne
  have hab : a ≠ b := fun h => hne (by rw [h])
  rcases hchk a ha b hb with h | h
  · exact hab h
  · have haN := hlt a ha
    have hc' : c = (2 * b + N - a) % N := by
      have h1 : ((2 * b + N - a) + a) % N = (c + a) % N := by
        have e : (2 * b + N - a) + a = (b + b) + N := by omega
        rw [e, Nat.add_mod_right, ← hv, Nat.add_comm]
      have h2 : (2 * b + N - a) % N = c % N := Nat.ModEq.add_right_cancel' a h1
      rw [Nat.mod_eq_of_lt (hlt c hc)] at h2
      exact h2.symm
    rw [hc'] at hc
    have := (testBit_mask L _).2 hc
    rw [this] at h
    exact Bool.noConfusion h

theorem card_cyc (N : ℕ) [NeZero N] (L : List ℕ) (hlt : ∀ a ∈ L, a < N) (hnd : L.Nodup) :
    (cyc N L).card = L.length := by
  unfold cyc
  rw [List.toFinset_card_of_nodup, List.length_map]
  refine hnd.map_on fun a ha b hb h => ?_
  have := congrArg Fin.val h
  rwa [val_res, val_res, Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at this

/-- An explicit 3-AP-free subset of `Z_N` bounds the Roth number of `Z_N`. -/
theorem le_addRothNumber_of_cyc (N : ℕ) [NeZero N] (L : List ℕ) {k : ℕ} (hk : L.length = k)
    (hlt : ∀ a ∈ L, a < N) (hnd : L.Nodup) (hchk : ∀ a ∈ L, ∀ b ∈ L, CycOk (mask L) N a b) :
    k ≤ addRothNumber (univ : Finset (Fin N)) := by
  rw [← hk, ← card_cyc N L hlt hnd]
  exact ThreeAPFree.le_addRothNumber (threeAPFree_cyc N L hlt hchk) (subset_univ _)

theorem z1 : 1 ≤ addRothNumber (univ : Finset (Fin 1)) :=
  le_addRothNumber_of_cyc 1 [0] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z3 : 2 ≤ addRothNumber (univ : Finset (Fin 3)) :=
  le_addRothNumber_of_cyc 3 [0, 1] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z7 : 3 ≤ addRothNumber (univ : Finset (Fin 7)) :=
  le_addRothNumber_of_cyc 7 [0, 1, 3] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z9 : 4 ≤ addRothNumber (univ : Finset (Fin 9)) :=
  le_addRothNumber_of_cyc 9 [0, 1, 3, 4] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z17 : 5 ≤ addRothNumber (univ : Finset (Fin 17)) :=
  le_addRothNumber_of_cyc 17 [0, 1, 3, 7, 8] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z19 : 6 ≤ addRothNumber (univ : Finset (Fin 19)) :=
  le_addRothNumber_of_cyc 19 [0, 1, 3, 12, 14, 15] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z21 : 6 ≤ addRothNumber (univ : Finset (Fin 21)) :=
  le_addRothNumber_of_cyc 21 [0, 1, 3, 4, 9, 10] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z25 : 7 ≤ addRothNumber (univ : Finset (Fin 25)) :=
  le_addRothNumber_of_cyc 25 [0, 1, 3, 4, 9, 10, 12] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z27 : 8 ≤ addRothNumber (univ : Finset (Fin 27)) :=
  le_addRothNumber_of_cyc 27 [0, 1, 3, 4, 9, 10, 12, 13] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z35 : 9 ≤ addRothNumber (univ : Finset (Fin 35)) :=
  le_addRothNumber_of_cyc 35 [0, 1, 3, 4, 10, 12, 22, 26, 28] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z37 : 10 ≤ addRothNumber (univ : Finset (Fin 37)) :=
  le_addRothNumber_of_cyc 37 [0, 1, 3, 7, 17, 24, 25, 28, 29, 35] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z39 : 10 ≤ addRothNumber (univ : Finset (Fin 39)) :=
  le_addRothNumber_of_cyc 39 [0, 1, 3, 7, 17, 25, 26, 29, 30, 37] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z45 : 10 ≤ addRothNumber (univ : Finset (Fin 45)) :=
  le_addRothNumber_of_cyc 45 [0, 1, 3, 4, 10, 14, 22, 32, 36, 38] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z47 : 10 ≤ addRothNumber (univ : Finset (Fin 47)) :=
  le_addRothNumber_of_cyc 47 [0, 1, 3, 4, 9, 11, 23, 33, 34, 39] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z51 : 11 ≤ addRothNumber (univ : Finset (Fin 51)) :=
  le_addRothNumber_of_cyc 51 [0, 1, 3, 4, 9, 13, 19, 20, 24, 41, 43] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z57 : 12 ≤ addRothNumber (univ : Finset (Fin 57)) :=
  le_addRothNumber_of_cyc 57 [0, 1, 3, 4, 9, 10, 12, 27, 37, 41, 43, 46] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z59 : 12 ≤ addRothNumber (univ : Finset (Fin 59)) :=
  le_addRothNumber_of_cyc 59 [0, 1, 3, 4, 9, 10, 12, 28, 38, 42, 43, 54] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z61 : 13 ≤ addRothNumber (univ : Finset (Fin 61)) :=
  le_addRothNumber_of_cyc 61 [0, 1, 3, 4, 9, 11, 29, 39, 42, 43, 46, 48, 51] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z63 : 13 ≤ addRothNumber (univ : Finset (Fin 63)) :=
  le_addRothNumber_of_cyc 63 [0, 1, 3, 4, 9, 10, 13, 28, 31, 42, 44, 48, 51] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z65 : 14 ≤ addRothNumber (univ : Finset (Fin 65)) :=
  le_addRothNumber_of_cyc 65 [0, 1, 3, 12, 14, 15, 17, 35, 37, 38, 42, 43, 45, 63] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z69 : 14 ≤ addRothNumber (univ : Finset (Fin 69)) :=
  le_addRothNumber_of_cyc 69 [0, 1, 3, 10, 11, 15, 16, 23, 25, 26, 28, 38, 57, 67] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z71 : 14 ≤ addRothNumber (univ : Finset (Fin 71)) :=
  le_addRothNumber_of_cyc 71 [0, 1, 3, 4, 9, 11, 31, 34, 35, 47, 49, 50, 52, 56] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z79 : 15 ≤ addRothNumber (univ : Finset (Fin 79)) :=
  le_addRothNumber_of_cyc 79 [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z81 : 16 ≤ addRothNumber (univ : Finset (Fin 81)) :=
  le_addRothNumber_of_cyc 81 [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z85 : 17 ≤ addRothNumber (univ : Finset (Fin 85)) :=
  le_addRothNumber_of_cyc 85 [0, 1, 3, 4, 9, 10, 13, 24, 28, 29, 31, 36, 40, 42, 50, 66, 73] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z93 : 17 ≤ addRothNumber (univ : Finset (Fin 93)) :=
  le_addRothNumber_of_cyc 93 [0, 1, 3, 4, 9, 11, 12, 16, 42, 61, 62, 65, 67, 70, 71, 74, 76] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z95 : 17 ≤ addRothNumber (univ : Finset (Fin 95)) :=
  le_addRothNumber_of_cyc 95 [0, 1, 3, 4, 9, 11, 12, 26, 27, 31, 33, 37, 38, 44, 46, 56, 78] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z97 : 17 ≤ addRothNumber (univ : Finset (Fin 97)) :=
  le_addRothNumber_of_cyc 97 [0, 1, 3, 4, 9, 10, 12, 22, 26, 28, 36, 38, 70, 74, 80, 82, 92] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem z99 : 17 ≤ addRothNumber (univ : Finset (Fin 99)) :=
  le_addRothNumber_of_cyc 99 [0, 1, 3, 4, 9, 10, 12, 13, 27, 29, 37, 43, 67, 75, 79, 81, 84] rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Every table entry is a lower bound for the Roth number of `Z_(2m+1)`. -/
theorem zt_le (m : ℕ) : zt (2 * m + 1) ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) := by
  rcases Nat.lt_or_ge m 50 with h | h
  · interval_cases m
    · rw [show zt (2 * 0 + 1) = 1 by decide +kernel]; exact z1
    · rw [show zt (2 * 1 + 1) = 2 by decide +kernel]; exact z3
    · rw [show zt (2 * 2 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 3 + 1) = 3 by decide +kernel]; exact z7
    · rw [show zt (2 * 4 + 1) = 4 by decide +kernel]; exact z9
    · rw [show zt (2 * 5 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 6 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 7 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 8 + 1) = 5 by decide +kernel]; exact z17
    · rw [show zt (2 * 9 + 1) = 6 by decide +kernel]; exact z19
    · rw [show zt (2 * 10 + 1) = 6 by decide +kernel]; exact z21
    · rw [show zt (2 * 11 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 12 + 1) = 7 by decide +kernel]; exact z25
    · rw [show zt (2 * 13 + 1) = 8 by decide +kernel]; exact z27
    · rw [show zt (2 * 14 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 15 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 16 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 17 + 1) = 9 by decide +kernel]; exact z35
    · rw [show zt (2 * 18 + 1) = 10 by decide +kernel]; exact z37
    · rw [show zt (2 * 19 + 1) = 10 by decide +kernel]; exact z39
    · rw [show zt (2 * 20 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 21 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 22 + 1) = 10 by decide +kernel]; exact z45
    · rw [show zt (2 * 23 + 1) = 10 by decide +kernel]; exact z47
    · rw [show zt (2 * 24 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 25 + 1) = 11 by decide +kernel]; exact z51
    · rw [show zt (2 * 26 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 27 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 28 + 1) = 12 by decide +kernel]; exact z57
    · rw [show zt (2 * 29 + 1) = 12 by decide +kernel]; exact z59
    · rw [show zt (2 * 30 + 1) = 13 by decide +kernel]; exact z61
    · rw [show zt (2 * 31 + 1) = 13 by decide +kernel]; exact z63
    · rw [show zt (2 * 32 + 1) = 14 by decide +kernel]; exact z65
    · rw [show zt (2 * 33 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 34 + 1) = 14 by decide +kernel]; exact z69
    · rw [show zt (2 * 35 + 1) = 14 by decide +kernel]; exact z71
    · rw [show zt (2 * 36 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 37 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 38 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 39 + 1) = 15 by decide +kernel]; exact z79
    · rw [show zt (2 * 40 + 1) = 16 by decide +kernel]; exact z81
    · rw [show zt (2 * 41 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 42 + 1) = 17 by decide +kernel]; exact z85
    · rw [show zt (2 * 43 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 44 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 45 + 1) = 0 by decide +kernel]; exact Nat.zero_le _
    · rw [show zt (2 * 46 + 1) = 17 by decide +kernel]; exact z93
    · rw [show zt (2 * 47 + 1) = 17 by decide +kernel]; exact z95
    · rw [show zt (2 * 48 + 1) = 17 by decide +kernel]; exact z97
    · rw [show zt (2 * 49 + 1) = 17 by decide +kernel]; exact z99
  · have h0 : zt (2 * m + 1) = 0 := by
      have n0 : 2 * m + 1 ≠ 1 := by omega
      have n1 : 2 * m + 1 ≠ 3 := by omega
      have n2 : 2 * m + 1 ≠ 7 := by omega
      have n3 : 2 * m + 1 ≠ 9 := by omega
      have n4 : 2 * m + 1 ≠ 17 := by omega
      have n5 : 2 * m + 1 ≠ 19 := by omega
      have n6 : 2 * m + 1 ≠ 21 := by omega
      have n7 : 2 * m + 1 ≠ 25 := by omega
      have n8 : 2 * m + 1 ≠ 27 := by omega
      have n9 : 2 * m + 1 ≠ 35 := by omega
      have n10 : 2 * m + 1 ≠ 37 := by omega
      have n11 : 2 * m + 1 ≠ 39 := by omega
      have n12 : 2 * m + 1 ≠ 45 := by omega
      have n13 : 2 * m + 1 ≠ 47 := by omega
      have n14 : 2 * m + 1 ≠ 51 := by omega
      have n15 : 2 * m + 1 ≠ 57 := by omega
      have n16 : 2 * m + 1 ≠ 59 := by omega
      have n17 : 2 * m + 1 ≠ 61 := by omega
      have n18 : 2 * m + 1 ≠ 63 := by omega
      have n19 : 2 * m + 1 ≠ 65 := by omega
      have n20 : 2 * m + 1 ≠ 69 := by omega
      have n21 : 2 * m + 1 ≠ 71 := by omega
      have n22 : 2 * m + 1 ≠ 79 := by omega
      have n23 : 2 * m + 1 ≠ 81 := by omega
      have n24 : 2 * m + 1 ≠ 85 := by omega
      have n25 : 2 * m + 1 ≠ 93 := by omega
      have n26 : 2 * m + 1 ≠ 95 := by omega
      have n27 : 2 * m + 1 ≠ 97 := by omega
      have n28 : 2 * m + 1 ≠ 99 := by omega
      unfold zt
      rw [if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6, if_neg n7, if_neg n8, if_neg n9, if_neg n10, if_neg n11, if_neg n12, if_neg n13, if_neg n14, if_neg n15, if_neg n16, if_neg n17, if_neg n18, if_neg n19, if_neg n20, if_neg n21, if_neg n22, if_neg n23, if_neg n24, if_neg n25, if_neg n26, if_neg n27, if_neg n28]
    rw [h0]; exact Nat.zero_le _

theorem zr_le (m : ℕ) : zr (2 * m + 1) ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) := by
  unfold zr
  refine max_le (zt_le m) ?_
  have e : (2 * m + 1 - 1) / 2 = m := by omega
  rw [e]
  calc V006.sz m ≤ rothNumberNat m := V006.sz_le m
    _ ≤ _ := by
        rw [← Fin.addRothNumber_eq_rothNumberNat (n := 2 * m) (k := m) le_rfl]
        exact addRothNumber.mono (subset_univ _)

/-! ### The tripartite construction with the cyclic table -/

open scoped Fin.CommRing in
/-- V007's `trip` with the Roth number of `Z_(2m+1)`. -/
theorem trip (m q r : ℕ) :
    ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r) *
      (zr (2 * m + 1) * addRothNumber (univ : Finset (Fin 6 → ZMod 3)) ^ q *
        addRothNumber (univ : Finset (Fin r → ZMod 3))) ≤
      ruzsaSzemerediNumberNat (3 * ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r)) := by
  have hcop : Nat.Coprime 2 (2 * m + 1) := by simp
  have hu1 : IsUnit (2 : Fin (2 * m + 1)) := by
    simpa using! (ZMod.unitOfCoprime 2 hcop).isUnit
  have hu3 : IsUnit (2 : ZMod 3) := ⟨⟨2, 2, by decide, by decide⟩, rfl⟩
  haveI : Fact (IsUnit (2 : V007.TG m q r)) := ⟨by
    rw [Prod.isUnit_iff, Prod.isUnit_iff]
    refine ⟨hu1, ?_, ?_⟩
    · rw [Pi.isUnit_iff]; intro i; rw [Pi.isUnit_iff]; intro j; exact hu3
    · rw [Pi.isUnit_iff]; intro i; exact hu3⟩
  have hcard : Fintype.card (V007.TG m q r) = (2 * m + 1) * 3 ^ (6 * q) * 3 ^ r := by
    simp [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card, pow_mul]; ring
  have h1 := zr_le m
  have h2 := V007.addRothNumber_univ_pow_le (H := Fin 6 → ZMod 3) q
  have h3 : zr (2 * m + 1) * addRothNumber (univ : Finset (Fin 6 → ZMod 3)) ^ q *
      addRothNumber (univ : Finset (Fin r → ZMod 3)) ≤
        addRothNumber (univ : Finset (V007.TG m q r)) := by
    calc _ ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) *
          addRothNumber (univ : Finset (Fin q → Fin 6 → ZMod 3)) *
          addRothNumber (univ : Finset (Fin r → ZMod 3)) := by gcongr
      _ ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) *
          addRothNumber (univ : Finset ((Fin q → Fin 6 → ZMod 3) × (Fin r → ZMod 3))) := by
          rw [mul_assoc]; gcongr; exact V007.addRothNumber_univ_prod_le
      _ ≤ addRothNumber (univ : Finset (V007.TG m q r)) := V007.addRothNumber_univ_prod_le
  have key := V007.rs_of_ring (V007.TG m q r)
  rw [hcard] at key
  exact (Nat.mul_le_mul_left _ h3).trans key

/-- The tripartite bound with the cap sizes of V007 and the cyclic table. -/
theorem trip_key (m k : ℕ) :
    3 ^ k * (2 * m + 1) * (V007.capB k * zr (2 * m + 1)) ≤
      SqueezeBench.RuzsaSzemeredi.f (3 * (3 ^ k * (2 * m + 1))) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r ≤ 5 ∧ k = 6 * q + r :=
    ⟨k / 6, k % 6, by omega, by omega⟩
  have hcap : V007.capB (6 * q + r) = 112 ^ q * V007.capr r := by
    unfold V007.capB
    have e1 : (6 * q + r) / 6 = q := by omega
    have e2 : (6 * q + r) % 6 = r := by omega
    rw [e1, e2]
  have h := trip m q r
  have h112 := V007.C112_le
  have hr' := V007.capr_le r hr
  have hpos : SqueezeBench.RuzsaSzemeredi.nMin ≤ 3 * (3 ^ (6 * q + r) * (2 * m + 1)) := by
    rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]
    exact Nat.le_mul_of_pos_right 3 (Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega))
  rw [SqueezeBench.RuzsaSzemeredi.f_of_le hpos]
  calc 3 ^ (6 * q + r) * (2 * m + 1) * (V007.capB (6 * q + r) * zr (2 * m + 1))
      = ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r) * (zr (2 * m + 1) * 112 ^ q * V007.capr r) := by
        rw [hcap, pow_add]; ring
    _ ≤ ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r) *
        (zr (2 * m + 1) * addRothNumber (univ : Finset (Fin 6 → ZMod 3)) ^ q *
          addRothNumber (univ : Finset (Fin r → ZMod 3))) := by gcongr
    _ ≤ ruzsaSzemerediNumberNat (3 * ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r)) := h
    _ = _ := by congr 1; rw [pow_add]; ring

/-- One term of the `max`: `3 · 3^k · (2m+1) ≤ 3 · 3^k · q` vertices suffice. -/
theorem term_le (m q k : ℕ) (hm : 2 * m + 1 ≤ q) :
    3 ^ k * V007.capB k * ((2 * m + 1) * zr (2 * m + 1)) ≤
      SqueezeBench.RuzsaSzemeredi.f (3 * 3 ^ k * q) := by
  have hpos : SqueezeBench.RuzsaSzemeredi.nMin ≤ 3 * (3 ^ k * (2 * m + 1)) := by
    rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]
    exact Nat.le_mul_of_pos_right 3 (Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega))
  calc 3 ^ k * V007.capB k * ((2 * m + 1) * zr (2 * m + 1))
      = 3 ^ k * (2 * m + 1) * (V007.capB k * zr (2 * m + 1)) := by ring
    _ ≤ SqueezeBench.RuzsaSzemeredi.f (3 * (3 ^ k * (2 * m + 1))) := trip_key m k
    _ ≤ SqueezeBench.RuzsaSzemeredi.f (3 * 3 ^ k * q) :=
        SqueezeBench.RuzsaSzemeredi.f_mono hpos (by rw [mul_assoc]; gcongr)

theorem tbAux_le (fuel : ℕ) : ∀ (m q k : ℕ), 2 * m + 1 ≤ q →
    3 ^ k * V007.capB k * tbAux fuel m ≤ SqueezeBench.RuzsaSzemeredi.f (3 * 3 ^ k * q) := by
  induction fuel with
  | zero => intro m q k _; simp [tbAux]
  | succ fuel ih =>
    intro m q k hm
    unfold tbAux
    rw [← Nat.mul_max_mul_left]
    exact max_le (term_le m q k hm) (ih (m - 1) q k (by omega))

theorem zbest_le (q k : ℕ) (hq : 1 ≤ q) :
    3 ^ k * V007.capB k * zbest q ≤ SqueezeBench.RuzsaSzemeredi.f (3 * 3 ^ k * q) := by
  unfold zbest
  simp only
  rw [← Nat.mul_max_mul_left]
  exact max_le (term_le _ q k (by omega)) (tbAux_le _ _ q k (by omega))

theorem tripAt_le (n k : ℕ) : tripAt n k ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  unfold tripAt
  simp only
  split_ifs with hq
  · exact Nat.zero_le _
  · have hq1 : 1 ≤ n / (3 * 3 ^ k) := Nat.one_le_iff_ne_zero.2 hq
    have hle : 3 * 3 ^ k * (n / (3 * 3 ^ k)) ≤ n := Nat.mul_div_le n _
    have hpos : SqueezeBench.RuzsaSzemeredi.nMin ≤ 3 * 3 ^ k * (n / (3 * 3 ^ k)) := by
      rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]
      exact (Nat.le_mul_of_pos_right 3 (Nat.pow_pos (by norm_num))).trans
        (Nat.le_mul_of_pos_right _ hq1)
    exact (zbest_le _ k hq1).trans (SqueezeBench.RuzsaSzemeredi.f_mono hpos hle)

theorem tripAux_le (fuel n : ℕ) : tripAux fuel n ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  induction fuel with
  | zero => exact tripAt_le n 0
  | succ k ih => exact max_le (tripAt_le n (k + 1)) ih

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f v :=
  fun n => tripAux_le _ n

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V007.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V007.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V007.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 21) (by decide)
    (by decide +kernel)

end SqueezeBench.RuzsaSzemeredi.Lower.V008
