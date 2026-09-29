import SqueezeBench.Problems.Ramsey.Records.Lower.V002.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V001.Proof

/-! Record V002 for Ramsey, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V002.lean`. The base relations `c5`, `c5c` and their properties
are reused from V001; the lexicographic power is generalised so that its innermost level
is an arbitrary relation, and instantiated with a block graph. -/

namespace SqueezeBench.Ramsey.Lower.V002

open SqueezeBench SimpleGraph

-- The `k`-fold lexicographic power of `b` over a base relation `e` at the innermost level.
def lexAdj (e b : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, x, y => e x y
  | k + 1, x, y => b (x % 5) (y % 5) || ((x % 5 == y % 5) && lexAdj e b k (x / 5) (y / 5))

theorem lexAdj_symm {e b : ℕ → ℕ → Bool}
    (hse : ∀ p q, e p q = true → e q p = true)
    (hs : ∀ p q, b p q = true → b q p = true) :
    ∀ k x y, lexAdj e b k x y = true → lexAdj e b k y x = true := by
  intro k
  induction k with
  | zero => intro x y h; exact hse _ _ h
  | succ k ih =>
    intro x y h
    simp [lexAdj] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hs _ _ h)
    · exact Or.inr ⟨h1.symm, ih _ _ h2⟩

theorem lexAdj_irrefl {e b : ℕ → ℕ → Bool} (hie : ∀ a, e a a = false)
    (hi : ∀ a, b a a = false) :
    ∀ k x, lexAdj e b k x x = false := by
  intro k
  induction k with
  | zero => intro x; exact hie x
  | succ k ih => intro x; simp [lexAdj, hi, ih]

-- Cliques of the `k`-fold power are at most `2^k` times as large as those of the base.
theorem clique_card {e b : ℕ → ℕ → Bool} (hi : ∀ a, b a a = false)
    (ht : ∀ p < 5, ∀ q < 5, ∀ r < 5, p ≠ q → q ≠ r → p ≠ r →
      b p q = true → b q r = true → b p r = false)
    (M c : ℕ)
    (he : ∀ S : Finset ℕ, (∀ x ∈ S, x < M) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → e x y = true) → S.card ≤ c) :
    ∀ k (S : Finset ℕ), (∀ x ∈ S, x < 5 ^ k * M) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → lexAdj e b k x y = true) → S.card ≤ 2 ^ k * c := by
  have key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 5) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → b x y = true) → T.card ≤ 2 := by
    intro T hT5 hTb
    by_contra hc
    obtain ⟨U, hUT, hU3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ T.card)
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hU3
    have hp : p ∈ T := hUT (by simp)
    have hq : q ∈ T := hUT (by simp)
    have hr : r ∈ T := hUT (by simp)
    have := ht p (hT5 p hp) q (hT5 q hq) r (hT5 r hr) hpq hqr hpr
      (hTb p hp q hq hpq) (hTb q hq r hr hqr)
    rw [hTb p hp r hr hpr] at this
    exact Bool.noConfusion this
  intro k
  induction k with
  | zero =>
    intro S hS hadj
    simpa using he S (by simpa using hS) (fun x hx y hy hxy => hadj x hx y hy hxy)
  | succ k ih =>
    intro S hS hadj
    have himg : (S.image (fun x => x % 5)).card ≤ 2 := by
      refine key _ ?_ ?_
      · intro a ha
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        omega
      · intro a ha c' hc' hac
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc'
        have hxy : x ≠ y := by rintro rfl; exact hac rfl
        have h := hadj x hx y hy hxy
        simp [lexAdj] at h
        rcases h with h | ⟨h1, _⟩
        · exact h
        · exact absurd h1 hac
    have hstep : (5 : ℕ) ^ (k + 1) * M = 5 * (5 ^ k * M) := by ring
    have hfib : ∀ a ∈ S.image (fun x => x % 5),
        (S.filter (fun x => x % 5 = a)).card ≤ 2 ^ k * c := by
      intro a _
      have hinj : Set.InjOn (fun x => x / 5) ↑(S.filter (fun x => x % 5 = a)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
        simp only at hxy
        omega
      rw [← Finset.card_image_of_injOn hinj]
      refine ih _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        have hx5 := hS x (Finset.mem_filter.mp hx).1
        rw [hstep] at hx5
        exact Nat.div_lt_of_lt_mul hx5
      · intro z hz w hw hzw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
        have hx' := Finset.mem_filter.mp hx
        have hy' := Finset.mem_filter.mp hy
        have hxy : x ≠ y := by rintro rfl; exact hzw rfl
        have h := hadj x hx'.1 y hy'.1 hxy
        simp [lexAdj] at h
        rcases h with h | ⟨_, h2⟩
        · rw [hx'.2, hy'.2, hi a] at h
          exact absurd h (by simp)
        · exact h2
    calc S.card ≤ 2 ^ k * c * (S.image (fun x => x % 5)).card :=
          Finset.card_le_mul_card_image S _ hfib
      _ ≤ 2 ^ k * c * 2 := Nat.mul_le_mul_left _ himg
      _ = 2 ^ (k + 1) * c := by ring

theorem lexAdj_dichotomy {e ec : ℕ → ℕ → Bool} (M : ℕ)
    (hed : ∀ x y, x < M → y < M → x ≠ y → e x y = true ∨ ec x y = true) :
    ∀ k x y, x < 5 ^ k * M → y < 5 ^ k * M → x ≠ y →
      lexAdj e V001.c5 k x y = true ∨ lexAdj ec V001.c5c k x y = true := by
  intro k
  induction k with
  | zero =>
    intro x y hx hy hxy
    simp only [pow_zero, one_mul] at hx hy
    exact hed x y hx hy hxy
  | succ k ih =>
    intro x y hx hy hxy
    have hstep : (5 : ℕ) ^ (k + 1) * M = 5 * (5 ^ k * M) := by ring
    rw [hstep] at hx hy
    by_cases hm : x % 5 = y % 5
    · have hdiv : x / 5 ≠ y / 5 := by
        intro h; exact hxy (by omega)
      have hx5 : x / 5 < 5 ^ k * M := Nat.div_lt_of_lt_mul hx
      have hy5 : y / 5 < 5 ^ k * M := Nat.div_lt_of_lt_mul hy
      rcases ih _ _ hx5 hy5 hdiv with h | h
      · exact Or.inl (by simp [lexAdj, hm, h])
      · exact Or.inr (by simp [lexAdj, hm, h])
    · by_cases hc : V001.c5 (x % 5) (y % 5) = true
      · exact Or.inl (by simp [lexAdj, hc])
      · exact Or.inr (by simp [lexAdj, V001.c5c, hm, hc])

-- The innermost level: `m` disjoint cliques of size `m`, and its complement.
def blk (m x y : ℕ) : Bool := !(x == y) && (x / m == y / m)

def blkc (m x y : ℕ) : Bool := !(x == y) && !(x / m == y / m)

theorem blk_irrefl (m : ℕ) : ∀ a, blk m a a = false := by intro a; simp [blk]

theorem blkc_irrefl (m : ℕ) : ∀ a, blkc m a a = false := by intro a; simp [blkc]

theorem blk_symm (m : ℕ) : ∀ p q, blk m p q = true → blk m q p = true := by
  intro p q h; simp [blk] at h ⊢; exact ⟨fun hh => h.1 hh.symm, h.2.symm⟩

theorem blkc_symm (m : ℕ) : ∀ p q, blkc m p q = true → blkc m q p = true := by
  intro p q h; simp [blkc] at h ⊢; exact ⟨fun hh => h.1 hh.symm, fun hh => h.2 hh.symm⟩

theorem blk_clique (m : ℕ) : ∀ S : Finset ℕ, (∀ x ∈ S, x < m * m) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → blk m x y = true) → S.card ≤ m := by
  intro S hS hadj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Finset.eq_empty_or_nonempty S with rfl | ⟨x, hx⟩
    · simp
    · have := hS x hx; omega
  · have hinj : Set.InjOn (fun x => x % m) ↑S := by
      intro x hx y hy hxy
      by_contra hne
      have h := hadj x hx y hy hne
      simp [blk] at h
      have hmod : x % m = y % m := hxy
      have : x = y := by
        rw [← Nat.div_add_mod x m, ← Nat.div_add_mod y m, h.2, hmod]
      exact hne this
    have hmaps : ∀ x ∈ S, x % m ∈ Finset.range m :=
      fun x _ => Finset.mem_range.mpr (Nat.mod_lt _ hm)
    simpa using Finset.card_le_card_of_injOn _ hmaps hinj

theorem blkc_clique (m : ℕ) : ∀ S : Finset ℕ, (∀ x ∈ S, x < m * m) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → blkc m x y = true) → S.card ≤ m := by
  intro S hS hadj
  have hinj : Set.InjOn (fun x => x / m) ↑S := by
    intro x hx y hy hxy
    by_contra hne
    have h := hadj x hx y hy hne
    simp [blkc] at h
    exact h.2 hxy
  have hmaps : ∀ x ∈ S, x / m ∈ Finset.range m := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (hS x hx))
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

theorem blk_dichotomy (m : ℕ) : ∀ x y, x < m * m → y < m * m → x ≠ y →
    blk m x y = true ∨ blkc m x y = true := by
  intro x y _ _ hxy
  by_cases h : x / m = y / m
  · exact Or.inl (by simp [blk, hxy, h])
  · exact Or.inr (by simp [blkc, hxy, h])

-- The graph on `Fin N` given by the construction with parameters `k` and `m`.
def GK (k m N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := lexAdj (blk m) V001.c5 k x.val y.val = true
  symm := ⟨fun _ _ h => lexAdj_symm (blk_symm m) V001.c5_symm k _ _ h⟩
  loopless := ⟨fun x h => by
    rw [lexAdj_irrefl (blk_irrefl m) V001.c5_irrefl k x.val] at h; exact Bool.noConfusion h⟩

theorem GK_adj {k m N : ℕ} {x y : Fin N} :
    (GK k m N).Adj x y ↔ lexAdj (blk m) V001.c5 k x.val y.val = true := Iff.rfl

theorem main {k m n : ℕ} (hn2 : 2 ≤ n) (h : 2 ^ k * m < n) : 5 ^ k * m ^ 2 + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hNle : N ≤ 5 ^ k * (m * m) := by
    have : 5 ^ k * m ^ 2 = 5 ^ k * (m * m) := by ring
    omega
  rcases hforces (GK k m N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := clique_card V001.c5_irrefl V001.c5_tri (m * m) m (blk_clique m) k
      (S.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hS.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact lt_of_lt_of_le z.isLt hNle
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ w := by rintro rfl; exact hxy rfl
      exact GK_adj.mp (hS.isClique hz hw hzw)
  · have hcard := clique_card V001.c5c_irrefl V001.c5c_tri (m * m) m (blkc_clique m) k
      (T.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hT.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact lt_of_lt_of_le z.isLt hNle
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ w := by rintro rfl; exact hxy rfl
      have hadj := hT.isClique hz hw hzw
      rw [compl_adj] at hadj
      have hz5 : (z : ℕ) < 5 ^ k * (m * m) := lt_of_lt_of_le z.isLt hNle
      have hw5 : (w : ℕ) < 5 ^ k * (m * m) := lt_of_lt_of_le w.isLt hNle
      rcases lexAdj_dichotomy (m * m) (blk_dichotomy m) k z.val w.val hz5 hw5 hxy with hd | hd
      · exact absurd (GK_adj.mpr hd) hadj.2
      · exact hd

theorem cand_le {n : ℕ} (hn2 : 2 ≤ n) (k : ℕ) : cand n k + 1 ≤ f n := by
  have hle : (n - 1) / 2 ^ k * 2 ^ k ≤ n - 1 := Nat.div_mul_le_self _ _
  have h : 2 ^ k * ((n - 1) / 2 ^ k) < n := by
    rw [Nat.mul_comm]
    omega
  simpa [cand] using main hn2 h

theorem bestUpTo_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ k, bestUpTo n k + 1 ≤ f n := by
  intro k
  induction k with
  | zero => simpa [bestUpTo] using cand_le hn2 0
  | succ k ih =>
    rw [bestUpTo]
    rcases Nat.le_total (cand n (k + 1)) (bestUpTo n k) with h | h
    · rw [Nat.max_eq_left h]; exact ih
    · rw [Nat.max_eq_right h]; exact cand_le hn2 (k + 1)

theorem w_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f w := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  exact bestUpTo_le hn2 n

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  maxWith_valid SqueezeBench.Ramsey.Lower.V001.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V001.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V001.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 13) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V002
