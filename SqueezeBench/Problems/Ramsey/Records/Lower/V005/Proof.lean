import SqueezeBench.Problems.Ramsey.Records.Lower.V005.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V004.Proof

/-! Record V005 for Ramsey, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V005.lean`. The base graph of the lexicographic construction is
the Paley graph on 37 vertices, which has no `K₅` and no independent 5-set; the block
graph at the innermost level and its two clique bounds come from V002, and the shape of
the argument from V003. -/

namespace SqueezeBench.Ramsey.Lower.V005

open SqueezeBench SimpleGraph

-- The quadratic residues mod 37.
def qr (z : ℕ) : Bool :=
  z == 1 || z == 3 || z == 4 || z == 7 || z == 9 || z == 10 || z == 11 || z == 12 ||
  z == 16 || z == 21 || z == 25 || z == 26 || z == 27 || z == 28 || z == 30 || z == 33 ||
  z == 34 || z == 36

-- The Paley graph on the residues mod 37, and its complement.
def pal (x y : ℕ) : Bool := qr ((y % 37 + 37 - x % 37) % 37)

def palc (x y : ℕ) : Bool := !(x % 37 == y % 37) && !(pal x y)

theorem pal_mod (x y : ℕ) : pal (x % 37) (y % 37) = pal x y := by
  simp only [pal, Nat.mod_mod]

theorem pal_irrefl : ∀ a, pal a a = false := by
  intro a
  simp only [pal]
  rw [show a % 37 + 37 - a % 37 = 37 from by omega]
  decide

theorem palc_irrefl : ∀ a, palc a a = false := by
  intro a; simp [palc]

theorem pal_symm_fin : ∀ p q : Fin 37, pal p q = true → pal q p = true := by decide

theorem pal_symm : ∀ p q, pal p q = true → pal q p = true := by
  intro p q h
  rw [← pal_mod] at h
  rw [← pal_mod]
  exact pal_symm_fin ⟨p % 37, Nat.mod_lt _ (by norm_num)⟩ ⟨q % 37, Nat.mod_lt _ (by norm_num)⟩ h

theorem palc_symm : ∀ p q, palc p q = true → palc q p = true := by
  intro p q h
  simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h ⊢
  refine ⟨fun hh => h.1 hh.symm, ?_⟩
  by_cases hqp : pal q p = true
  · have h2 := pal_symm q p hqp
    rw [h.2] at h2
    exact Bool.noConfusion h2
  · exact Bool.not_eq_true _ |>.mp hqp

theorem pal_dichotomy : ∀ x y, x < 37 * 1 → y < 37 * 1 → x ≠ y →
    pal x y = true ∨ palc x y = true := by
  intro x y hx hy hxy
  by_cases h : pal x y = true
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    exact ⟨by omega, Bool.not_eq_true _ |>.mp h⟩

-- Translating by `a` is an automorphism of the Paley graph: the difference is unchanged.
theorem pal_translate {a x y : ℕ} (ha : a < 37) (hx : x < 37) (hy : y < 37) :
    pal ((x + 37 - a) % 37) ((y + 37 - a) % 37) = pal x y := by
  simp only [pal, Nat.mod_mod]
  congr 1
  omega

theorem palc_translate {a x y : ℕ} (ha : a < 37) (hx : x < 37) (hy : y < 37)
    (h : palc x y = true) : palc ((x + 37 - a) % 37) ((y + 37 - a) % 37) = true := by
  simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h ⊢
  refine ⟨by omega, ?_⟩
  rw [pal_translate ha hx hy]
  exact h.2

-- The neighbourhood of `0` is the set of residues, and it carries no `K₄`. The adjacency
-- hypotheses come before the quantifiers they constrain, so the check stops early.
theorem qr_k4_free :
    ∀ p ∈ ([1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List ℕ),
    ∀ q ∈ ([1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List ℕ),
    pal p q = true →
    ∀ r ∈ ([1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List ℕ),
    pal p r = true → pal q r = true →
    ∀ s ∈ ([1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List ℕ),
    pal p s = true → pal q s = true → pal r s = true → False := by decide

-- The same for the complement: the non-residues carry no `K₄` of `palc`.
theorem nqr_k4_free :
    ∀ p ∈ ([2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35] : List ℕ),
    ∀ q ∈ ([2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35] : List ℕ),
    palc p q = true →
    ∀ r ∈ ([2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35] : List ℕ),
    palc p r = true → palc q r = true →
    ∀ s ∈ ([2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35] : List ℕ),
    palc p s = true → palc q s = true → palc r s = true → False := by decide

theorem qr_mem {a x : ℕ} (ha : a < 37) (hx : x < 37) (h : pal a x = true) :
    (x + 37 - a) % 37 ∈
      ([1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List ℕ) := by
  simp only [pal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hx] at h
  simp only [qr, Bool.or_eq_true, beq_iff_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem nqr_mem {a x : ℕ} (ha : a < 37) (hx : x < 37) (h : palc a x = true) :
    (x + 37 - a) % 37 ∈
      ([2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35] : List ℕ) := by
  simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨hne, hfalse⟩ := h
  simp only [pal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hx] at hfalse
  simp only [qr, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hfalse
  have h0 : (x + 37 - a) % 37 ≠ 0 := by omega
  have hlt : (x + 37 - a) % 37 < 37 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

-- Neither colour of the Paley graph has a clique of size 5: a `K₅` through `a` translates
-- to `0` together with a `K₄` inside the neighbourhood of `0`.
theorem pal_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 37 * 1) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → pal x y = true) → T.card ≤ 4 := by
  intro T hT hadj
  by_contra hc
  obtain ⟨U, hUT, hU5⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ T.card)
  obtain ⟨a, ha⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
  have h4 : (U.erase a).card = 4 := by rw [Finset.card_erase_of_mem ha, hU5]
  obtain ⟨p, hp⟩ : (U.erase a).Nonempty := Finset.card_pos.mp (by omega)
  have h3 : ((U.erase a).erase p).card = 3 := by rw [Finset.card_erase_of_mem hp, h4]
  obtain ⟨q, r, s, hqr, hqs, hrs, hU3⟩ := Finset.card_eq_three.mp h3
  have hqm : q ∈ (U.erase a).erase p := by rw [hU3]; simp
  have hrm : r ∈ (U.erase a).erase p := by rw [hU3]; simp
  have hsm : s ∈ (U.erase a).erase p := by rw [hU3]; simp
  have haT : a ∈ T := hUT ha
  have hpT : p ∈ T := hUT (Finset.mem_of_mem_erase hp)
  have hqT : q ∈ T := hUT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqm))
  have hrT : r ∈ T := hUT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hrm))
  have hsT : s ∈ T := hUT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hsm))
  have haL : a < 37 := by have := hT a haT; omega
  have hpL : p < 37 := by have := hT p hpT; omega
  have hqL : q < 37 := by have := hT q hqT; omega
  have hrL : r < 37 := by have := hT r hrT; omega
  have hsL : s < 37 := by have := hT s hsT; omega
  have hap : a ≠ p := fun h => (Finset.ne_of_mem_erase hp) h.symm
  have haq : a ≠ q := fun h =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqm)) h.symm
  have har : a ≠ r := fun h =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hrm)) h.symm
  have has : a ≠ s := fun h =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hsm)) h.symm
  have hpq : p ≠ q := fun h => (Finset.ne_of_mem_erase hqm) h.symm
  have hpr : p ≠ r := fun h => (Finset.ne_of_mem_erase hrm) h.symm
  have hps : p ≠ s := fun h => (Finset.ne_of_mem_erase hsm) h.symm
  refine qr_k4_free _ (qr_mem haL hpL (hadj a haT p hpT hap)) _
    (qr_mem haL hqL (hadj a haT q hqT haq)) ?_ _
    (qr_mem haL hrL (hadj a haT r hrT har)) ?_ ?_ _
    (qr_mem haL hsL (hadj a haT s hsT has)) ?_ ?_ ?_
  · rw [pal_translate haL hpL hqL]; exact hadj p hpT q hqT hpq
  · rw [pal_translate haL hpL hrL]; exact hadj p hpT r hrT hpr
  · rw [pal_translate haL hqL hrL]; exact hadj q hqT r hrT hqr
  · rw [pal_translate haL hpL hsL]; exact hadj p hpT s hsT hps
  · rw [pal_translate haL hqL hsL]; exact hadj q hqT s hsT hqs
  · rw [pal_translate haL hrL hsL]; exact hadj r hrT s hsT hrs

theorem palc_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 37 * 1) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → palc x y = true) → T.card ≤ 4 := by
  intro T hT hadj
  by_contra hc
  obtain ⟨U, hUT, hU5⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ T.card)
  obtain ⟨a, ha⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
  have h4 : (U.erase a).card = 4 := by rw [Finset.card_erase_of_mem ha, hU5]
  obtain ⟨p, hp⟩ : (U.erase a).Nonempty := Finset.card_pos.mp (by omega)
  have h3 : ((U.erase a).erase p).card = 3 := by rw [Finset.card_erase_of_mem hp, h4]
  obtain ⟨q, r, s, hqr, hqs, hrs, hU3⟩ := Finset.card_eq_three.mp h3
  have hqm : q ∈ (U.erase a).erase p := by rw [hU3]; simp
  have hrm : r ∈ (U.erase a).erase p := by rw [hU3]; simp
  have hsm : s ∈ (U.erase a).erase p := by rw [hU3]; simp
  have haT : a ∈ T := hUT ha
  have hpT : p ∈ T := hUT (Finset.mem_of_mem_erase hp)
  have hqT : q ∈ T := hUT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqm))
  have hrT : r ∈ T := hUT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hrm))
  have hsT : s ∈ T := hUT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hsm))
  have haL : a < 37 := by have := hT a haT; omega
  have hpL : p < 37 := by have := hT p hpT; omega
  have hqL : q < 37 := by have := hT q hqT; omega
  have hrL : r < 37 := by have := hT r hrT; omega
  have hsL : s < 37 := by have := hT s hsT; omega
  have hap : a ≠ p := fun h => (Finset.ne_of_mem_erase hp) h.symm
  have haq : a ≠ q := fun h =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqm)) h.symm
  have har : a ≠ r := fun h =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hrm)) h.symm
  have has : a ≠ s := fun h =>
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hsm)) h.symm
  have hpq : p ≠ q := fun h => (Finset.ne_of_mem_erase hqm) h.symm
  have hpr : p ≠ r := fun h => (Finset.ne_of_mem_erase hrm) h.symm
  have hps : p ≠ s := fun h => (Finset.ne_of_mem_erase hsm) h.symm
  exact nqr_k4_free _ (nqr_mem haL hpL (hadj a haT p hpT hap)) _
    (nqr_mem haL hqL (hadj a haT q hqT haq))
    (palc_translate haL hpL hqL (hadj p hpT q hqT hpq)) _
    (nqr_mem haL hrL (hadj a haT r hrT har))
    (palc_translate haL hpL hrL (hadj p hpT r hrT hpr))
    (palc_translate haL hqL hrL (hadj q hqT r hrT hqr)) _
    (nqr_mem haL hsL (hadj a haT s hsT has))
    (palc_translate haL hpL hsL (hadj p hpT s hsT hps))
    (palc_translate haL hqL hsL (hadj q hqT s hsT hqs))
    (palc_translate haL hrL hsL (hadj r hrT s hsT hrs))

-- The `k`-fold lexicographic power of `b` over a base relation `e` at the innermost level.
def lexAdj (e b : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, x, y => e x y
  | k + 1, x, y => b (x % 37) (y % 37) || ((x % 37 == y % 37) && lexAdj e b k (x / 37) (y / 37))

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

-- Cliques of the `k`-fold power are at most `4^k` times as large as those of the base.
theorem clique_card {e b : ℕ → ℕ → Bool} (hi : ∀ a, b a a = false)
    (hkey : ∀ T : Finset ℕ, (∀ x ∈ T, x < 37 * 1) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → b x y = true) → T.card ≤ 4)
    (M c : ℕ)
    (he : ∀ S : Finset ℕ, (∀ x ∈ S, x < M) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → e x y = true) → S.card ≤ c) :
    ∀ k (S : Finset ℕ), (∀ x ∈ S, x < 37 ^ k * M) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → lexAdj e b k x y = true) → S.card ≤ 4 ^ k * c := by
  intro k
  induction k with
  | zero =>
    intro S hS hadj
    simpa using he S (by simpa using hS) (fun x hx y hy hxy => hadj x hx y hy hxy)
  | succ k ih =>
    intro S hS hadj
    have himg : (S.image (fun x => x % 37)).card ≤ 4 := by
      refine hkey _ ?_ ?_
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
    have hstep : (37 : ℕ) ^ (k + 1) * M = 37 * (37 ^ k * M) := by ring
    have hfib : ∀ a ∈ S.image (fun x => x % 37),
        (S.filter (fun x => x % 37 = a)).card ≤ 4 ^ k * c := by
      intro a _
      have hinj : Set.InjOn (fun x => x / 37) ↑(S.filter (fun x => x % 37 = a)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
        simp only at hxy
        omega
      rw [← Finset.card_image_of_injOn hinj]
      refine ih _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        have hx37 := hS x (Finset.mem_filter.mp hx).1
        rw [hstep] at hx37
        exact Nat.div_lt_of_lt_mul hx37
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
    calc S.card ≤ 4 ^ k * c * (S.image (fun x => x % 37)).card :=
          Finset.card_le_mul_card_image S _ hfib
      _ ≤ 4 ^ k * c * 4 := Nat.mul_le_mul_left _ himg
      _ = 4 ^ (k + 1) * c := by ring

theorem lexAdj_dichotomy {e ec : ℕ → ℕ → Bool} (M : ℕ)
    (hed : ∀ x y, x < M → y < M → x ≠ y → e x y = true ∨ ec x y = true) :
    ∀ k x y, x < 37 ^ k * M → y < 37 ^ k * M → x ≠ y →
      lexAdj e pal k x y = true ∨ lexAdj ec palc k x y = true := by
  intro k
  induction k with
  | zero =>
    intro x y hx hy hxy
    simp only [pow_zero, one_mul] at hx hy
    exact hed x y hx hy hxy
  | succ k ih =>
    intro x y hx hy hxy
    have hstep : (37 : ℕ) ^ (k + 1) * M = 37 * (37 ^ k * M) := by ring
    rw [hstep] at hx hy
    by_cases hm : x % 37 = y % 37
    · have hdiv : x / 37 ≠ y / 37 := by
        intro h; exact hxy (by omega)
      have hx37 : x / 37 < 37 ^ k * M := Nat.div_lt_of_lt_mul hx
      have hy37 : y / 37 < 37 ^ k * M := Nat.div_lt_of_lt_mul hy
      rcases ih _ _ hx37 hy37 hdiv with h | h
      · exact Or.inl (by simp [lexAdj, hm, h])
      · exact Or.inr (by simp [lexAdj, hm, h])
    · by_cases hc : pal (x % 37) (y % 37) = true
      · exact Or.inl (by simp [lexAdj, hc])
      · refine Or.inr ?_
        simp only [lexAdj, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
        refine Or.inl ?_
        simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        exact ⟨by omega, Bool.not_eq_true _ |>.mp hc⟩

-- The graph on `Fin N` given by the construction with parameters `k` and `m`.
def GK (k m N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := lexAdj (V002.blk m) pal k x.val y.val = true
  symm := ⟨fun _ _ h => lexAdj_symm (V002.blk_symm m) pal_symm k _ _ h⟩
  loopless := ⟨fun x h => by
    rw [lexAdj_irrefl (V002.blk_irrefl m) pal_irrefl k x.val] at h; exact Bool.noConfusion h⟩

theorem GK_adj {k m N : ℕ} {x y : Fin N} :
    (GK k m N).Adj x y ↔ lexAdj (V002.blk m) pal k x.val y.val = true := Iff.rfl

theorem main {k m n : ℕ} (hn2 : 2 ≤ n) (h : 4 ^ k * m < n) : 37 ^ k * m ^ 2 + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hNle : N ≤ 37 ^ k * (m * m) := by
    have : 37 ^ k * m ^ 2 = 37 ^ k * (m * m) := by ring
    omega
  rcases hforces (GK k m N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := clique_card pal_irrefl pal_key (m * m) m (V002.blk_clique m) k
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
  · have hcard := clique_card palc_irrefl palc_key (m * m) m (V002.blkc_clique m) k
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
      have hz37 : (z : ℕ) < 37 ^ k * (m * m) := lt_of_lt_of_le z.isLt hNle
      have hw37 : (w : ℕ) < 37 ^ k * (m * m) := lt_of_lt_of_le w.isLt hNle
      rcases lexAdj_dichotomy (m * m) (V002.blk_dichotomy m) k z.val w.val hz37 hw37 hxy with hd | hd
      · exact absurd (GK_adj.mpr hd) hadj.2
      · exact hd

theorem go_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel j, go (n - 1) fuel (4 ^ j) (37 ^ j) + 1 ≤ f n := by
  have h1 : (1 : ℕ) ≤ f n := by
    have := main (k := 0) (m := 0) hn2 (by simpa using by omega)
    simpa using this
  intro fuel
  induction fuel with
  | zero => intro j; simpa [go] using h1
  | succ fuel ih =>
    intro j
    rw [go]
    by_cases hlt : n - 1 < 4 ^ j
    · simpa [hlt] using h1
    · rw [if_neg hlt]
      have hterm : 37 ^ j * ((n - 1) / 4 ^ j) ^ 2 + 1 ≤ f n := by
        have hle : (n - 1) / 4 ^ j * 4 ^ j ≤ n - 1 := Nat.div_mul_le_self _ _
        refine main hn2 ?_
        rw [Nat.mul_comm]
        omega
      have hnext : go (n - 1) fuel (4 * 4 ^ j) (37 * 37 ^ j) + 1 ≤ f n := by
        have := ih (j + 1)
        rw [pow_succ, pow_succ] at this
        rw [Nat.mul_comm (4 ^ j) 4, Nat.mul_comm (37 ^ j) 37] at this
        exact this
      rcases Nat.le_total (37 ^ j * ((n - 1) / 4 ^ j) ^ 2)
          (go (n - 1) fuel (4 * 4 ^ j) (37 * 37 ^ j)) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact hterm

theorem w_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f w := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  have := go_le hn2 n 0
  simpa using this

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  maxWith_valid SqueezeBench.Ramsey.Lower.V004.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V004.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V004.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 5) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V005
