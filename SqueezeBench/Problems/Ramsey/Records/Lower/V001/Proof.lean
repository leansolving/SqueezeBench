import SqueezeBench.Problems.Ramsey.Records.Lower.V001.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V000.Proof

/-! Record V001 for Ramsey, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V001.lean`. -/

namespace SqueezeBench.Ramsey.Lower.V001

open SqueezeBench SimpleGraph

-- The 5-cycle on the residues mod 5, and its complement, as boolean relations on `ℕ`.
def c5 (p q : ℕ) : Bool := ((p + 1) % 5 == q % 5) || ((q + 1) % 5 == p % 5)

def c5c (p q : ℕ) : Bool := !(p == q) && !(c5 p q)

-- The `k`-fold lexicographic power of a base relation, on base-5 digits: the least
-- significant digit decides, and ties are broken by the remaining digits.
def lexAdj (b : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | k + 1, x, y => b (x % 5) (y % 5) || ((x % 5 == y % 5) && lexAdj b k (x / 5) (y / 5))

theorem lexAdj_symm {b : ℕ → ℕ → Bool} (hs : ∀ p q, b p q = true → b q p = true) :
    ∀ k x y, lexAdj b k x y = true → lexAdj b k y x = true := by
  intro k
  induction k with
  | zero => intro x y h; simp [lexAdj] at h
  | succ k ih =>
    intro x y h
    simp [lexAdj] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hs _ _ h)
    · exact Or.inr ⟨h1.symm, ih _ _ h2⟩

theorem lexAdj_irrefl {b : ℕ → ℕ → Bool} (hi : ∀ a, b a a = false) :
    ∀ k x, lexAdj b k x x = false := by
  intro k
  induction k with
  | zero => intro x; simp [lexAdj]
  | succ k ih => intro x; simp [lexAdj, hi, ih]

-- Any triangle-free base relation bounds the cliques of its lexicographic powers.
theorem clique_card {b : ℕ → ℕ → Bool} (hi : ∀ a, b a a = false)
    (ht : ∀ p < 5, ∀ q < 5, ∀ r < 5, p ≠ q → q ≠ r → p ≠ r →
      b p q = true → b q r = true → b p r = false) :
    ∀ k (S : Finset ℕ), (∀ x ∈ S, x < 5 ^ k) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → lexAdj b k x y = true) → S.card ≤ 2 ^ k := by
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
    intro S hS _
    have hsub : S ⊆ {0} := by
      intro x hx
      have := hS x hx
      simp at this ⊢
      omega
    have := Finset.card_le_card hsub
    simpa using this
  | succ k ih =>
    intro S hS hadj
    have himg : (S.image (fun x => x % 5)).card ≤ 2 := by
      refine key _ ?_ ?_
      · intro a ha
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        omega
      · intro a ha c hc hac
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
        have hxy : x ≠ y := by rintro rfl; exact hac rfl
        have h := hadj x hx y hy hxy
        simp [lexAdj] at h
        rcases h with h | ⟨h1, _⟩
        · exact h
        · exact absurd h1 hac
    have hfib : ∀ a ∈ S.image (fun x => x % 5),
        (S.filter (fun x => x % 5 = a)).card ≤ 2 ^ k := by
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
        refine Nat.div_lt_of_lt_mul ?_
        rw [pow_succ] at hx5
        omega
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
    calc S.card ≤ 2 ^ k * (S.image (fun x => x % 5)).card :=
          Finset.card_le_mul_card_image S _ hfib
      _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_left _ himg
      _ = 2 ^ (k + 1) := by ring

-- `c5` and `c5c` split every pair of distinct vertices between them.
theorem lexAdj_dichotomy : ∀ k x y, x < 5 ^ k → y < 5 ^ k → x ≠ y →
    lexAdj c5 k x y = true ∨ lexAdj c5c k x y = true := by
  intro k
  induction k with
  | zero => intro x y hx hy hxy; simp at hx hy; omega
  | succ k ih =>
    intro x y hx hy hxy
    by_cases hm : x % 5 = y % 5
    · have hdiv : x / 5 ≠ y / 5 := by
        intro h; exact hxy (by omega)

      have hx5 : x / 5 < 5 ^ k := by
        refine Nat.div_lt_of_lt_mul ?_
        rw [pow_succ] at hx; omega
      have hy5 : y / 5 < 5 ^ k := by
        refine Nat.div_lt_of_lt_mul ?_
        rw [pow_succ] at hy; omega
      rcases ih _ _ hx5 hy5 hdiv with h | h
      · exact Or.inl (by simp [lexAdj, hm, h])
      · exact Or.inr (by simp [lexAdj, hm, h])
    · by_cases hc : c5 (x % 5) (y % 5) = true
      · exact Or.inl (by simp [lexAdj, hc])
      · refine Or.inr (by simp [lexAdj, c5c, hm, hc])

theorem c5_irrefl : ∀ a, c5 a a = false := by
  intro a; simp [c5]; omega

theorem c5c_irrefl : ∀ a, c5c a a = false := by
  intro a; simp [c5c]

theorem c5_symm : ∀ p q, c5 p q = true → c5 q p = true := by
  intro p q h; simp [c5] at h ⊢; tauto

theorem c5_tri_fin : ∀ p q r : Fin 5, (p : ℕ) ≠ (q : ℕ) → (q : ℕ) ≠ (r : ℕ) →
    (p : ℕ) ≠ (r : ℕ) →
    c5 p q = true → c5 q r = true → c5 p r = false := by decide

theorem c5c_tri_fin : ∀ p q r : Fin 5, (p : ℕ) ≠ (q : ℕ) → (q : ℕ) ≠ (r : ℕ) →
    (p : ℕ) ≠ (r : ℕ) →
    c5c p q = true → c5c q r = true → c5c p r = false := by decide

theorem c5_tri : ∀ p < 5, ∀ q < 5, ∀ r < 5, p ≠ q → q ≠ r → p ≠ r →
    c5 p q = true → c5 q r = true → c5 p r = false :=
  fun p hp q hq r hr => c5_tri_fin ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩

theorem c5c_tri : ∀ p < 5, ∀ q < 5, ∀ r < 5, p ≠ q → q ≠ r → p ≠ r →
    c5c p q = true → c5c q r = true → c5c p r = false :=
  fun p hp q hq r hr => c5c_tri_fin ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩

-- The graph on `Fin N` whose vertices are read as `k` base-5 digits.
def G5 (k N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := lexAdj c5 k x.val y.val = true
  symm := ⟨fun _ _ h => lexAdj_symm c5_symm k _ _ h⟩
  loopless := ⟨fun x h => by
    rw [lexAdj_irrefl c5_irrefl k x.val] at h; exact Bool.noConfusion h⟩

theorem G5_adj {k N : ℕ} {x y : Fin N} :
    (G5 k N).Adj x y ↔ lexAdj c5 k x.val y.val = true := Iff.rfl

theorem pow5_le_f {k n : ℕ} (h : 2 ^ k < n) : 5 ^ k + 1 ≤ f n := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hn : nMin ≤ n := by simp [nMin]; omega
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hNle : N ≤ 5 ^ k := by omega
  rcases hforces (G5 k N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := clique_card c5_irrefl c5_tri k (S.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hS.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact lt_of_lt_of_le z.isLt hNle
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ w := by rintro rfl; exact hxy rfl
      exact G5_adj.mp (hS.isClique hz hw hzw)
  · have hcard := clique_card c5c_irrefl c5c_tri k (T.image (fun z : Fin N => z.val)) ?_ ?_
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
      have hz5 : (z : ℕ) < 5 ^ k := lt_of_lt_of_le z.isLt hNle
      have hw5 : (w : ℕ) < 5 ^ k := lt_of_lt_of_le w.isLt hNle
      rcases lexAdj_dichotomy k z.val w.val hz5 hw5 hxy with hd | hd
      · exact absurd (G5_adj.mpr hd) hadj.2
      · exact hd

theorem blog_pow_le : ∀ fuel m : ℕ, 1 ≤ m → 2 ^ blog fuel m ≤ m := by
  intro fuel
  induction fuel with
  | zero => intro m hm; simpa [blog] using hm
  | succ fuel ih =>
    intro m hm
    rw [blog]
    by_cases h : m < 2
    · simpa [h] using hm
    · rw [if_neg h, pow_succ]
      have := ih (m / 2) (by omega)
      have h2 : m / 2 * 2 ≤ m := Nat.div_mul_le_self m 2
      calc 2 ^ blog fuel (m / 2) * 2 ≤ m / 2 * 2 := Nat.mul_le_mul_right _ this
        _ ≤ m := h2

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  have := blog_pow_le n (n - 1) (by omega)
  exact pow5_le_f (by omega)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  maxWith_valid SqueezeBench.Ramsey.Lower.V000.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V000.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V000.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 5) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V001
