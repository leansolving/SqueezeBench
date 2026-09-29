import SqueezeBench.Problems.Ramsey.Records.Lower.V004.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V003.Proof

/-! Record V004 for Ramsey, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V004.lean`. Nothing new is constructed here: the lexicographic
power of V002 (base the 5-cycle) is stacked on the lexicographic power of V003 (base the
Paley graph on 17 vertices) on the block graph of V002, which all three lemmas of V002 and
V003 already allow, since they are generic in the innermost relation. -/

namespace SqueezeBench.Ramsey.Lower.V004

open SqueezeBench SimpleGraph

-- `a` levels of the 5-cycle over `b` levels of the Paley graph over `m` blocks of size `m`.
def mixed (a b m : ℕ) : ℕ → ℕ → Bool :=
  V002.lexAdj (V003.lexAdj (V002.blk m) V003.pal b) V001.c5 a

def mixedc (a b m : ℕ) : ℕ → ℕ → Bool :=
  V002.lexAdj (V003.lexAdj (V002.blkc m) V003.palc b) V001.c5c a

def GM (a b m N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := mixed a b m x.val y.val = true
  symm := ⟨fun _ _ h =>
    V002.lexAdj_symm (V003.lexAdj_symm (V002.blk_symm m) V003.pal_symm b) V001.c5_symm a _ _ h⟩
  loopless := ⟨fun x h => by
    simp only [mixed] at h
    rw [V002.lexAdj_irrefl (V003.lexAdj_irrefl (V002.blk_irrefl m) V003.pal_irrefl b)
      V001.c5_irrefl a x.val] at h
    exact Bool.noConfusion h⟩

theorem GM_adj {a b m N : ℕ} {x y : Fin N} :
    (GM a b m N).Adj x y ↔ mixed a b m x.val y.val = true := Iff.rfl

theorem main {a b m n : ℕ} (hn2 : 2 ≤ n) (h : 2 ^ a * (3 ^ b * m) < n) :
    5 ^ a * (17 ^ b * m ^ 2) + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hNle : N ≤ 5 ^ a * (17 ^ b * (m * m)) := by
    have he : 5 ^ a * (17 ^ b * m ^ 2) = 5 ^ a * (17 ^ b * (m * m)) := by ring
    omega
  have hinner : ∀ S : Finset ℕ, (∀ x ∈ S, x < 17 ^ b * (m * m)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → V003.lexAdj (V002.blk m) V003.pal b x y = true) →
      S.card ≤ 3 ^ b * m :=
    V003.clique_card V003.pal_irrefl V003.pal_key (m * m) m (V002.blk_clique m) b
  have hinnerc : ∀ S : Finset ℕ, (∀ x ∈ S, x < 17 ^ b * (m * m)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → V003.lexAdj (V002.blkc m) V003.palc b x y = true) →
      S.card ≤ 3 ^ b * m :=
    V003.clique_card V003.palc_irrefl V003.palc_key (m * m) m (V002.blkc_clique m) b
  rcases hforces (GM a b m N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := V002.clique_card V001.c5_irrefl V001.c5_tri (17 ^ b * (m * m)) (3 ^ b * m)
      hinner a (S.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hS.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact lt_of_lt_of_le z.isLt hNle
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨wv, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ wv := by rintro rfl; exact hxy rfl
      exact GM_adj.mp (hS.isClique hz hw hzw)
  · have hcard := V002.clique_card V001.c5c_irrefl V001.c5c_tri (17 ^ b * (m * m)) (3 ^ b * m)
      hinnerc a (T.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hT.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact lt_of_lt_of_le z.isLt hNle
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨wv, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ wv := by rintro rfl; exact hxy rfl
      have hadj := hT.isClique hz hw hzw
      rw [compl_adj] at hadj
      have hz5 : (z : ℕ) < 5 ^ a * (17 ^ b * (m * m)) := lt_of_lt_of_le z.isLt hNle
      have hw5 : (wv : ℕ) < 5 ^ a * (17 ^ b * (m * m)) := lt_of_lt_of_le wv.isLt hNle
      rcases V002.lexAdj_dichotomy (17 ^ b * (m * m))
        (V003.lexAdj_dichotomy (m * m) (V002.blk_dichotomy m) b) a z.val wv.val hz5 hw5 hxy with
        hd | hd
      · exact absurd (GM_adj.mpr hd) hadj.2
      · exact hd

theorem term_le {n : ℕ} (hn2 : 2 ≤ n) (a b : ℕ) :
    5 ^ a * 17 ^ b * ((n - 1) / (2 ^ a * 3 ^ b)) ^ 2 + 1 ≤ f n := by
  have hpos : 0 < 2 ^ a * 3 ^ b :=
    Nat.mul_pos (pow_pos (by norm_num) a) (pow_pos (by norm_num) b)
  have hle : (n - 1) / (2 ^ a * 3 ^ b) * (2 ^ a * 3 ^ b) ≤ n - 1 := Nat.div_mul_le_self _ _
  have hmain := main (a := a) (b := b) (m := (n - 1) / (2 ^ a * 3 ^ b)) hn2 (by
    have : 2 ^ a * (3 ^ b * ((n - 1) / (2 ^ a * 3 ^ b))) =
        (n - 1) / (2 ^ a * 3 ^ b) * (2 ^ a * 3 ^ b) := by ring
    omega)
  have he : 5 ^ a * (17 ^ b * ((n - 1) / (2 ^ a * 3 ^ b)) ^ 2) =
      5 ^ a * 17 ^ b * ((n - 1) / (2 ^ a * 3 ^ b)) ^ 2 := by ring
  omega

theorem one_le {n : ℕ} (hn2 : 2 ≤ n) : (1 : ℕ) ≤ f n := by
  have := main (a := 0) (b := 0) (m := 0) hn2 (by simpa using by omega)
  simpa using this

theorem goB_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel a b,
    goB (n - 1) fuel (2 ^ a * 3 ^ b) (5 ^ a * 17 ^ b) + 1 ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro a b; simpa [goB] using one_le hn2
  | succ fuel ih =>
    intro a b
    rw [goB]
    by_cases hlt : n - 1 < 2 ^ a * 3 ^ b
    · simpa [hlt] using one_le hn2
    · rw [if_neg hlt]
      have hnext := ih a (b + 1)
      rw [pow_succ 3 b, pow_succ 17 b] at hnext
      rw [show 2 ^ a * (3 ^ b * 3) = 3 * (2 ^ a * 3 ^ b) from by ring,
        show 5 ^ a * (17 ^ b * 17) = 17 * (5 ^ a * 17 ^ b) from by ring] at hnext
      rcases Nat.le_total (5 ^ a * 17 ^ b * ((n - 1) / (2 ^ a * 3 ^ b)) ^ 2)
          (goB (n - 1) fuel (3 * (2 ^ a * 3 ^ b)) (17 * (5 ^ a * 17 ^ b))) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact term_le hn2 a b

theorem goA_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel a,
    goA (n - 1) fuel (2 ^ a) (5 ^ a) + 1 ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro a; simpa [goA] using one_le hn2
  | succ fuel ih =>
    intro a
    rw [goA]
    by_cases hlt : n - 1 < 2 ^ a
    · simpa [hlt] using one_le hn2
    · rw [if_neg hlt]
      have hB := goB_le hn2 (fuel + 1) a 0
      simp only [pow_zero, Nat.mul_one] at hB
      have hnext := ih (a + 1)
      rw [pow_succ 2 a, pow_succ 5 a] at hnext
      rw [show 2 ^ a * 2 = 2 * 2 ^ a from by ring, show 5 ^ a * 5 = 5 * 5 ^ a from by ring]
        at hnext
      rcases Nat.le_total (goB (n - 1) (fuel + 1) (2 ^ a) (5 ^ a))
          (goA (n - 1) fuel (2 * 2 ^ a) (5 * 5 ^ a)) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact hB

theorem w_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f w := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  have := goA_le hn2 n 0
  simpa using this

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  maxWith_valid SqueezeBench.Ramsey.Lower.V003.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V003.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V003.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 7) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V004
