import SqueezeBench.Problems.Roth.Records.Lower.V007.Def
import SqueezeBench.Problems.Roth.Records.Lower.V006.Proof

/-! Record V007 for Roth, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Roth/Lower/V007.lean`. -/

namespace SqueezeBench.Roth.Lower.V007

open SqueezeBench Finset

/-- One explicit 3-AP-free subset of `[0, n)` of size `r₃(n)` for each jump node `n` of `r₃`
(every `n ≤ 209` with `r₃(n) > r₃(n-1)`), largest first, and the empty set for `n = 0`: the
sets of OEIS A003002's a-file, shifted from `{1, …, n}` to `{0, …, n-1}`. Between two jump
nodes the earlier set still has the right size, so these certify every entry of `tblList`. -/
def certs : List (ℕ × List ℕ) :=
  [(209, [0, 1, 6, 8, 9, 13, 19, 21, 22, 24, 28, 45, 49, 51, 52, 54, 60, 64, 65, 67, 72, 73, 88, 139, 141, 142, 147, 149, 158, 161, 162, 165, 178, 179, 184, 186, 187, 192, 199, 201, 202, 204, 208]),
   (204, [0, 2, 3, 5, 12, 14, 17, 18, 30, 35, 44, 45, 50, 51, 54, 59, 61, 62, 66, 69, 75, 128, 134, 137, 141, 142, 144, 149, 152, 153, 158, 159, 168, 173, 185, 186, 189, 191, 198, 200, 201, 203]),
   (194, [0, 2, 6, 7, 13, 15, 16, 21, 22, 39, 43, 45, 46, 48, 54, 58, 59, 61, 66, 67, 82, 131, 133, 138, 139, 141, 146, 150, 152, 155, 156, 168, 170, 175, 176, 178, 183, 187, 189, 192, 193]),
   (174, [0, 1, 4, 6, 10, 15, 17, 18, 23, 25, 37, 38, 41, 43, 47, 52, 54, 55, 60, 62, 111, 112, 115, 117, 121, 126, 128, 129, 134, 136, 148, 149, 152, 154, 158, 163, 165, 166, 171, 173]),
   (169, [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53, 57, 67, 111, 112, 115, 116, 122, 124, 125, 127, 131, 141, 148, 149, 152, 153, 159, 161, 162, 164, 168]),
   (165, [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53, 57, 67, 111, 112, 115, 116, 122, 124, 125, 127, 131, 141, 148, 149, 152, 153, 159, 161, 162, 164]),
   (163, [0, 1, 3, 9, 10, 13, 14, 21, 31, 35, 37, 38, 40, 46, 47, 50, 51, 58, 68, 72, 111, 112, 114, 120, 121, 124, 125, 132, 142, 146, 148, 149, 151, 157, 158, 161, 162]),
   (157, [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53, 57, 67, 111, 112, 115, 116, 122, 124, 125, 127, 131, 141, 144, 145, 148, 153, 154, 156]),
   (150, [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53, 57, 104, 107, 108, 111, 116, 117, 119, 120, 135, 137, 138, 140, 144, 146, 147, 149]),
   (145, [0, 4, 6, 7, 9, 15, 16, 19, 20, 35, 37, 43, 44, 46, 47, 52, 56, 62, 99, 101, 102, 107, 110, 111, 114, 116, 128, 132, 134, 135, 137, 141, 143, 144]),
   (137, [0, 1, 3, 4, 12, 14, 15, 19, 22, 31, 33, 36, 42, 45, 46, 49, 55, 82, 85, 93, 99, 100, 102, 103, 108, 112, 120, 126, 127, 129, 130, 135, 136]),
   (122, [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40, 81, 82, 84, 85, 90, 91, 93, 94, 108, 109, 111, 112, 117, 118, 120, 121]),
   (121, [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40, 81, 82, 84, 85, 90, 91, 93, 94, 108, 109, 111, 112, 117, 118, 120]),
   (114, [0, 1, 3, 8, 11, 12, 17, 18, 27, 29, 30, 32, 39, 44, 45, 68, 69, 74, 81, 83, 84, 86, 95, 96, 101, 102, 105, 110, 112, 113]),
   (111, [0, 3, 4, 7, 12, 16, 18, 22, 27, 30, 31, 34, 39, 43, 45, 67, 69, 73, 80, 81, 84, 85, 92, 94, 98, 105, 106, 109, 110]),
   (104, [0, 4, 6, 9, 10, 13, 15, 23, 25, 28, 29, 32, 34, 38, 65, 69, 71, 74, 75, 78, 80, 88, 90, 93, 94, 97, 99, 103]),
   (100, [0, 4, 6, 9, 10, 13, 15, 23, 25, 28, 29, 32, 34, 38, 65, 69, 71, 74, 75, 78, 80, 88, 90, 93, 94, 97, 99]),
   (95, [0, 1, 3, 4, 9, 13, 19, 21, 24, 28, 30, 31, 40, 54, 63, 64, 66, 70, 73, 75, 81, 85, 90, 91, 93, 94]),
   (92, [0, 1, 7, 8, 11, 12, 18, 20, 26, 27, 30, 31, 38, 57, 63, 66, 67, 70, 72, 80, 82, 85, 86, 89, 91]),
   (84, [0, 2, 3, 7, 8, 15, 17, 20, 21, 24, 29, 36, 47, 54, 59, 62, 63, 66, 68, 75, 76, 80, 81, 83]),
   (82, [0, 1, 3, 7, 8, 10, 18, 21, 22, 25, 27, 30, 48, 56, 58, 61, 62, 65, 67, 70, 77, 80, 81]),
   (74, [0, 1, 6, 8, 9, 13, 19, 21, 22, 24, 28, 45, 49, 51, 52, 54, 60, 64, 65, 67, 72, 73]),
   (71, [0, 2, 3, 7, 8, 17, 18, 22, 23, 25, 30, 40, 45, 49, 51, 54, 56, 64, 66, 69, 70]),
   (63, [0, 1, 4, 6, 10, 15, 17, 18, 23, 25, 37, 38, 41, 43, 47, 52, 54, 55, 60, 62]),
   (58, [0, 4, 6, 7, 9, 15, 16, 19, 20, 27, 37, 41, 43, 44, 46, 52, 53, 56, 57]),
   (54, [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53]),
   (51, [0, 1, 4, 5, 11, 13, 14, 16, 20, 34, 37, 38, 41, 43, 46, 47, 50]),
   (41, [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40]),
   (40, [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39]),
   (36, [0, 1, 4, 6, 9, 10, 13, 15, 23, 27, 28, 32, 34, 35]),
   (32, [0, 1, 4, 6, 9, 10, 13, 21, 23, 24, 28, 30, 31]),
   (30, [0, 2, 3, 7, 8, 10, 19, 21, 22, 26, 27, 29]),
   (26, [0, 2, 3, 7, 8, 10, 15, 19, 21, 24, 25]),
   (24, [0, 1, 4, 6, 10, 15, 17, 18, 22, 23]),
   (20, [0, 1, 5, 6, 8, 13, 14, 17, 19]),
   (14, [0, 1, 3, 4, 9, 10, 12, 13]),
   (13, [0, 1, 3, 4, 9, 10, 12]),
   (11, [0, 1, 3, 4, 9, 10]),
   (9, [0, 1, 3, 7, 8]),
   (5, [0, 1, 3, 4]),
   (4, [0, 1, 3]),
   (2, [0, 1]),
   (1, [0]),
   (0, [])]

/-- The bitmask of a list: bit `x` is set for each `x` in the list. -/
def mask (l : List ℕ) : ℕ := l.foldl (fun m x => m ||| (1 <<< x)) 0

/-- The quadratic 3-AP check: for every `a < b` in `l`, the third term `2b - a` is not in `m`. -/
def chk (l : List ℕ) (m : ℕ) : Bool :=
  l.all (fun a => l.all (fun b => decide (b ≤ a) || !(m.testBit (2 * b - a))))

/-- Every certificate is duplicate-free, passes the pair check against its own mask, and every
element is in that mask. -/
def certOK : Bool :=
  certs.all (fun p => decide p.2.Nodup && chk p.2 (mask p.2)
    && p.2.all (fun x => (mask p.2).testBit x))

/-- Every table entry `n ≤ 209` is at most the number of elements below `n` of the first
certificate whose jump node is at most `n`. -/
def tblOK : Bool :=
  (List.range 210).all (fun n => certs.any (fun p =>
    decide (p.1 ≤ n) && decide (tbl n ≤ SqueezeBench.Roth.Lower.V004.below p.2 n)))

theorem certOK_eq : certOK = true := by decide +kernel

theorem tblOK_eq : tblOK = true := by decide +kernel

-- the pair check certifies that `l` has no three-term progression: a progression `a, b, c` with
-- `a ≠ c` has its lower endpoint below `b`, and the check rules out its upper endpoint
theorem free_of_chk {l : List ℕ} {m : ℕ} (h : chk l m = true)
    (hm : ∀ x ∈ l, m.testBit x = true) :
    ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, a + c = b + b → a = c := by
  simp only [chk, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  intro a ha b hb c hc habc
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := h a ha b hb
    have hba : ¬ b ≤ a := by omega
    have h2 : m.testBit (2 * b - a) = false := by tauto
    have h3 : 2 * b - a = c := by omega
    rw [h3, hm c hc] at h2
    exact Bool.true_eq_false.mp h2 |>.elim
  · have h1 := h c hc b hb
    have hbc : ¬ b ≤ c := by omega
    have h2 : m.testBit (2 * b - c) = false := by tauto
    have h3 : 2 * b - c = a := by omega
    rw [h3, hm a ha] at h2
    exact Bool.true_eq_false.mp h2 |>.elim

-- every certificate is a 3-AP-free set, so each of its prefixes bounds `f`
theorem certs_le : ∀ p ∈ certs, ∀ n, SqueezeBench.Roth.Lower.V004.below p.2 n ≤ SqueezeBench.Roth.f n := by
  have h := certOK_eq
  simp only [certOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  intro p hp n
  obtain ⟨⟨hnd, hchk⟩, hbit⟩ := h p hp
  exact SqueezeBench.Roth.Lower.V004.below_le p.2 hnd (free_of_chk hchk hbit) n

theorem tblList_length : tblList.length = 210 := by rfl

theorem tbl_le (n : ℕ) : tbl n ≤ SqueezeBench.Roth.f n := by
  rcases Nat.lt_or_ge n 210 with hn | hn
  · have h := tblOK_eq
    simp only [tblOK, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨p, hp, -, hle⟩ := h n hn
    exact le_trans hle (certs_le p hp n)
  · have h0 : tbl n = 0 := by
      simp only [tbl]
      exact List.getD_eq_default _ _ (by rw [tblList_length]; exact hn)
    rw [h0]
    exact Nat.zero_le _

-- monotonicity of `f`: the top of the base window survives to every larger `n`
theorem tbl209_le {n : ℕ} (hn : 209 ≤ n) : tbl 209 ≤ SqueezeBench.Roth.f n :=
  le_trans (tbl_le 209) (SqueezeBench.Roth.f_mono (show SqueezeBench.Roth.nMin ≤ 209 by simp) hn)

theorem cntAux_le : ∀ fuel n : ℕ, n ≤ fuel → cntAux fuel n ≤ SqueezeBench.Roth.f n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simp [cntAux, SqueezeBench.Roth.f]
  | succ fuel ih =>
    intro n hn
    rw [cntAux]
    split
    · exact tbl_le n
    · rename_i h209
      refine max_le (tbl209_le (by omega)) ?_
      have h₁ := ih ((n + 2) / 3) (by omega)
      have h₂ := ih ((n + 1) / 3) (by omega)
      have := SqueezeBench.Roth.Lower.V002.split_le n (by omega)
      omega

theorem cnt_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f cnt :=
  fun n => cntAux_le n n le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Roth.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Roth.Lower.V006.valid cnt_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Roth.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Roth.nMin SqueezeBench.Roth.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Roth.nMin) (n₀ := 209) (by decide)
    (by decide +kernel)

end SqueezeBench.Roth.Lower.V007
