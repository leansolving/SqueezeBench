import SqueezeBench.Problems.Ramsey.Records.Lower.V008.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V007.Proof

/-! Record V008 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V008.lean`. The construction is the lexicographic stacking of
V004, extended by a fourth base, the Paley graph on 101 vertices (no `K₆` in either
colour, the graph behind `R(6,6) > 101`), and all four bases are mixed. The lexicographic
power is proved once, generic in the modulus and the base clique bound, and instantiated at
5, 17, 37 and 101 with the base facts of V001, V003, V005 and this file. The new
certificate uses V005's translation argument (a `K₆` through `a` becomes `0` with a `K₅`
inside the residues) and a fuel-driven depth-first clique checker whose soundness is
proved by induction, so the kernel only evaluates the checker on the fifty residues. -/

namespace SqueezeBench.Ramsey.Lower.V008

open SqueezeBench SimpleGraph

/-! ## A clique checker -/

-- `cliqueFree adj fuel k L = true` certifies that no `k` distinct elements of `L` are
-- pairwise related by `adj`: cliques through the head are cliques of its neighbours in the
-- tail, one size down. Structural in `fuel` so that the kernel unfolds it directly.
def cliqueFree (adj : ℕ → ℕ → Bool) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => false
  | _ + 1, 0, _ => false
  | _ + 1, _ + 1, [] => true
  | fuel + 1, k + 1, x :: xs =>
      cliqueFree adj fuel k (xs.filter (adj x)) && cliqueFree adj fuel (k + 1) xs

theorem cliqueFree_sound (adj : ℕ → ℕ → Bool) : ∀ fuel k (L : List ℕ),
    cliqueFree adj fuel k L = true →
    ∀ S : Finset ℕ, (∀ x ∈ S, x ∈ L) → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → adj x y = true) →
    S.card < k := by
  intro fuel
  induction fuel with
  | zero => intro k L h; simp [cliqueFree] at h
  | succ fuel ih =>
    intro k L h S hSL hS
    cases k with
    | zero => simp [cliqueFree] at h
    | succ k =>
      cases L with
      | nil =>
        rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
        · simp
        · exact absurd (hSL y hy) (by simp)
      | cons x xs =>
        simp only [cliqueFree, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        by_cases hx : x ∈ S
        · have hcard := ih k (xs.filter (adj x)) h1 (S.erase x) ?_ ?_
          · rw [Finset.card_erase_of_mem hx] at hcard
            omega
          · intro y hy
            have hyS := Finset.mem_of_mem_erase hy
            have hyx := Finset.ne_of_mem_erase hy
            rw [List.mem_filter]
            refine ⟨?_, hS x hx y hyS (Ne.symm hyx)⟩
            have := hSL y hyS
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hyx
            · exact h
          · intro y hy z hz hyz
            exact hS y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hyz
        · refine ih (k + 1) xs h2 S ?_ hS
          intro y hy
          have := hSL y hy
          simp only [List.mem_cons] at this
          rcases this with h | h
          · exact absurd (h ▸ hy) hx
          · exact h

/-! ## The Paley graph on 101 vertices -/

-- The quadratic residues mod 101, as a bitmask: bit `z` is set iff `z` is a residue.
def qr (z : ℕ) : Bool := (1550432784880709368503235994226 >>> z) % 2 == 1

-- The Paley graph on the residues mod 101, and its complement.
def pal (x y : ℕ) : Bool := qr ((y % 101 + 101 - x % 101) % 101)

def palc (x y : ℕ) : Bool := !(x % 101 == y % 101) && !(pal x y)

def qrList : List ℕ :=
  [1, 4, 5, 6, 9, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 36, 37, 43, 45, 47,
   49, 52, 54, 56, 58, 64, 65, 68, 70, 71, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 92, 95,
   96, 97, 100]

def nqrList : List ℕ :=
  [2, 3, 7, 8, 10, 11, 12, 15, 18, 26, 27, 28, 29, 32, 34, 35, 38, 39, 40, 41, 42, 44, 46, 48,
   50, 51, 53, 55, 57, 59, 60, 61, 62, 63, 66, 67, 69, 72, 73, 74, 75, 83, 86, 89, 90, 91, 93,
   94, 98, 99]

theorem qr_zero : qr 0 = false := by decide

-- `−1` is a residue mod 101, so the residues are closed under negation.
theorem qr_neg_fin : ∀ d : Fin 101, qr ((101 - (d : ℕ)) % 101) = qr d := by decide

theorem qr_neg : ∀ d, d < 101 → qr ((101 - d) % 101) = qr d :=
  fun d hd => qr_neg_fin ⟨d, hd⟩

theorem qr_mem_fin : ∀ d : Fin 101, qr d = true → (d : ℕ) ∈ qrList := by decide +kernel

theorem nqr_mem_fin : ∀ d : Fin 101, (d : ℕ) ≠ 0 → qr d = false → (d : ℕ) ∈ nqrList := by
  decide +kernel

-- The neighbourhood of `0` in either colour carries no `K₅`.
theorem qr_k5_free : cliqueFree pal 60 5 qrList = true := by decide +kernel

theorem nqr_k5_free : cliqueFree palc 60 5 nqrList = true := by decide +kernel

theorem pal_irrefl : ∀ a, pal a a = false := by
  intro a
  simp only [pal]
  rw [show (a % 101 + 101 - a % 101) % 101 = 0 from by omega]
  exact qr_zero

theorem palc_irrefl : ∀ a, palc a a = false := by
  intro a; simp [palc]

theorem pal_symm : ∀ p q, pal p q = true → pal q p = true := by
  intro p q h
  simp only [pal] at h ⊢
  rw [show (p % 101 + 101 - q % 101) % 101 = (101 - (q % 101 + 101 - p % 101) % 101) % 101 from
    by omega, qr_neg _ (Nat.mod_lt _ (by norm_num))]
  exact h

theorem palc_symm : ∀ p q, palc p q = true → palc q p = true := by
  intro p q h
  simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h ⊢
  refine ⟨fun hh => h.1 hh.symm, ?_⟩
  by_cases hqp : pal q p = true
  · have h2 := pal_symm q p hqp
    rw [h.2] at h2
    exact Bool.noConfusion h2
  · exact Bool.not_eq_true _ |>.mp hqp

theorem pal_dichotomy : ∀ x y, x < 101 → y < 101 → x ≠ y →
    pal x y = true ∨ palc x y = true := by
  intro x y hx hy hxy
  by_cases h : pal x y = true
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    exact ⟨by omega, Bool.not_eq_true _ |>.mp h⟩

-- Translating by `a` is an automorphism of the Paley graph: the difference is unchanged.
theorem pal_translate {a x y : ℕ} (ha : a < 101) (hx : x < 101) (hy : y < 101) :
    pal ((x + 101 - a) % 101) ((y + 101 - a) % 101) = pal x y := by
  simp only [pal, Nat.mod_mod]
  congr 1
  omega

theorem palc_translate {a x y : ℕ} (ha : a < 101) (hx : x < 101) (hy : y < 101)
    (h : palc x y = true) : palc ((x + 101 - a) % 101) ((y + 101 - a) % 101) = true := by
  simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h ⊢
  refine ⟨by omega, ?_⟩
  rw [pal_translate ha hx hy]
  exact h.2

theorem qr_mem {a x : ℕ} (ha : a < 101) (hx : x < 101) (h : pal a x = true) :
    (x + 101 - a) % 101 ∈ qrList := by
  simp only [pal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hx] at h
  exact qr_mem_fin ⟨(x + 101 - a) % 101, Nat.mod_lt _ (by norm_num)⟩ h

theorem nqr_mem {a x : ℕ} (ha : a < 101) (hx : x < 101) (h : palc a x = true) :
    (x + 101 - a) % 101 ∈ nqrList := by
  simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨hne, hfalse⟩ := h
  simp only [pal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hx] at hfalse
  have h0 : (x + 101 - a) % 101 ≠ 0 := by omega
  exact nqr_mem_fin ⟨(x + 101 - a) % 101, Nat.mod_lt _ (by norm_num)⟩ h0 hfalse

-- Neither colour has a clique of size 6: a `K₆` through `a` translates to `0` together with
-- a `K₅` inside the neighbourhood of `0`, which the checker rules out.
theorem pal_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 101) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → pal x y = true) → T.card ≤ 5 := by
  intro T hT hadj
  by_contra hc
  obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have haL : a < 101 := hT a ha
  have hinj : Set.InjOn (fun x => (x + 101 - a) % 101) ↑(T.erase a) := by
    intro x hx y hy hxy
    have hxL := hT x (Finset.mem_of_mem_erase hx)
    have hyL := hT y (Finset.mem_of_mem_erase hy)
    simp only at hxy
    omega
  have hcard := cliqueFree_sound pal 60 5 qrList qr_k5_free
    ((T.erase a).image (fun x => (x + 101 - a) % 101)) ?_ ?_
  · rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem ha] at hcard
    omega
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact qr_mem haL (hT x (Finset.mem_of_mem_erase hx))
      (hadj a ha x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm)
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by rintro rfl; exact hzw rfl
    rw [pal_translate haL (hT x (Finset.mem_of_mem_erase hx)) (hT y (Finset.mem_of_mem_erase hy))]
    exact hadj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy

theorem palc_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 101) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → palc x y = true) → T.card ≤ 5 := by
  intro T hT hadj
  by_contra hc
  obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have haL : a < 101 := hT a ha
  have hinj : Set.InjOn (fun x => (x + 101 - a) % 101) ↑(T.erase a) := by
    intro x hx y hy hxy
    have hxL := hT x (Finset.mem_of_mem_erase hx)
    have hyL := hT y (Finset.mem_of_mem_erase hy)
    simp only at hxy
    omega
  have hcard := cliqueFree_sound palc 60 5 nqrList nqr_k5_free
    ((T.erase a).image (fun x => (x + 101 - a) % 101)) ?_ ?_
  · rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem ha] at hcard
    omega
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact nqr_mem haL (hT x (Finset.mem_of_mem_erase hx))
      (hadj a ha x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm)
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by rintro rfl; exact hzw rfl
    exact palc_translate haL (hT x (Finset.mem_of_mem_erase hx))
      (hT y (Finset.mem_of_mem_erase hy))
      (hadj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)

/-! ## The lexicographic power, generic in the modulus -/

-- The `k`-fold lexicographic power of `b` (a relation on the residues mod `q`) over a base
-- relation `e` at the innermost level: the least significant base-`q` digit decides, and
-- ties are broken by the remaining digits.
def lexAdj (q : ℕ) (e b : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, x, y => e x y
  | k + 1, x, y => b (x % q) (y % q) || ((x % q == y % q) && lexAdj q e b k (x / q) (y / q))

theorem lexAdj_symm (q : ℕ) {e b : ℕ → ℕ → Bool}
    (hse : ∀ p q, e p q = true → e q p = true)
    (hs : ∀ p q, b p q = true → b q p = true) :
    ∀ k x y, lexAdj q e b k x y = true → lexAdj q e b k y x = true := by
  intro k
  induction k with
  | zero => intro x y h; exact hse _ _ h
  | succ k ih =>
    intro x y h
    simp [lexAdj] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hs _ _ h)
    · exact Or.inr ⟨h1.symm, ih _ _ h2⟩

theorem lexAdj_irrefl (q : ℕ) {e b : ℕ → ℕ → Bool} (hie : ∀ a, e a a = false)
    (hi : ∀ a, b a a = false) :
    ∀ k x, lexAdj q e b k x x = false := by
  intro k
  induction k with
  | zero => intro x; exact hie x
  | succ k ih => intro x; simp [lexAdj, hi, ih]

-- Cliques of the `k`-fold power are at most `cq^k` times as large as those of the base,
-- when the relation on the residues has no clique larger than `cq`.
theorem clique_card (q cq : ℕ) (hq : 0 < q) {e b : ℕ → ℕ → Bool} (hi : ∀ a, b a a = false)
    (hkey : ∀ T : Finset ℕ, (∀ x ∈ T, x < q) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → b x y = true) → T.card ≤ cq)
    (M c : ℕ)
    (he : ∀ S : Finset ℕ, (∀ x ∈ S, x < M) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → e x y = true) → S.card ≤ c) :
    ∀ k (S : Finset ℕ), (∀ x ∈ S, x < q ^ k * M) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → lexAdj q e b k x y = true) → S.card ≤ cq ^ k * c := by
  intro k
  induction k with
  | zero =>
    intro S hS hadj
    simpa using he S (by simpa using hS) (fun x hx y hy hxy => hadj x hx y hy hxy)
  | succ k ih =>
    intro S hS hadj
    have himg : (S.image (fun x => x % q)).card ≤ cq := by
      refine hkey _ ?_ ?_
      · intro a ha
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        exact Nat.mod_lt _ hq
      · intro a ha c' hc' hac
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc'
        have hxy : x ≠ y := by rintro rfl; exact hac rfl
        have h := hadj x hx y hy hxy
        simp [lexAdj] at h
        rcases h with h | ⟨h1, _⟩
        · exact h
        · exact absurd h1 hac
    have hstep : q ^ (k + 1) * M = q * (q ^ k * M) := by ring
    have hfib : ∀ a ∈ S.image (fun x => x % q),
        (S.filter (fun x => x % q = a)).card ≤ cq ^ k * c := by
      intro a _
      have hinj : Set.InjOn (fun x => x / q) ↑(S.filter (fun x => x % q = a)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
        simp only at hxy
        calc x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
          _ = q * (y / q) + y % q := by rw [hxy, hx.2, hy.2]
          _ = y := Nat.div_add_mod y q
      rw [← Finset.card_image_of_injOn hinj]
      refine ih _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        have hxq := hS x (Finset.mem_filter.mp hx).1
        rw [hstep] at hxq
        exact Nat.div_lt_of_lt_mul hxq
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
    calc S.card ≤ cq ^ k * c * (S.image (fun x => x % q)).card :=
          Finset.card_le_mul_card_image S _ hfib
      _ ≤ cq ^ k * c * cq := Nat.mul_le_mul_left _ himg
      _ = cq ^ (k + 1) * c := by ring

-- Two relations that split every pair of distinct residues split every pair of distinct
-- vertices of the power, given innermost relations that do the same.
theorem lexAdj_dichotomy (q : ℕ) {e ec b bc : ℕ → ℕ → Bool} (M : ℕ)
    (hed : ∀ x y, x < M → y < M → x ≠ y → e x y = true ∨ ec x y = true)
    (hbd : ∀ x y, x < q → y < q → x ≠ y → b x y = true ∨ bc x y = true) (hq : 0 < q) :
    ∀ k x y, x < q ^ k * M → y < q ^ k * M → x ≠ y →
      lexAdj q e b k x y = true ∨ lexAdj q ec bc k x y = true := by
  intro k
  induction k with
  | zero =>
    intro x y hx hy hxy
    simp only [pow_zero, one_mul] at hx hy
    exact hed x y hx hy hxy
  | succ k ih =>
    intro x y hx hy hxy
    have hstep : q ^ (k + 1) * M = q * (q ^ k * M) := by ring
    rw [hstep] at hx hy
    by_cases hm : x % q = y % q
    · have hdiv : x / q ≠ y / q := by
        intro h
        apply hxy
        calc x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
          _ = q * (y / q) + y % q := by rw [h, hm]
          _ = y := Nat.div_add_mod y q
      have hxq : x / q < q ^ k * M := Nat.div_lt_of_lt_mul hx
      have hyq : y / q < q ^ k * M := Nat.div_lt_of_lt_mul hy
      rcases ih _ _ hxq hyq hdiv with h | h
      · exact Or.inl (by simp [lexAdj, hm, h])
      · exact Or.inr (by simp [lexAdj, hm, h])
    · rcases hbd (x % q) (y % q) (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) hm with h | h
      · exact Or.inl (by simp [lexAdj, h])
      · exact Or.inr (by simp [lexAdj, h])

/-! ## The base facts of the 5-cycle in the generic form -/

theorem c5_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 5) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → V001.c5 x y = true) → T.card ≤ 2 := by
  intro T hT5 hTb
  by_contra hc
  obtain ⟨U, hUT, hU3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ T.card)
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hU3
  have hp : p ∈ T := hUT (by simp)
  have hq : q ∈ T := hUT (by simp)
  have hr : r ∈ T := hUT (by simp)
  have := V001.c5_tri p (hT5 p hp) q (hT5 q hq) r (hT5 r hr) hpq hqr hpr
    (hTb p hp q hq hpq) (hTb q hq r hr hqr)
  rw [hTb p hp r hr hpr] at this
  exact Bool.noConfusion this

theorem c5c_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 5) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → V001.c5c x y = true) → T.card ≤ 2 := by
  intro T hT5 hTb
  by_contra hc
  obtain ⟨U, hUT, hU3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ T.card)
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hU3
  have hp : p ∈ T := hUT (by simp)
  have hq : q ∈ T := hUT (by simp)
  have hr : r ∈ T := hUT (by simp)
  have := V001.c5c_tri p (hT5 p hp) q (hT5 q hq) r (hT5 r hr) hpq hqr hpr
    (hTb p hp q hq hpq) (hTb q hq r hr hqr)
  rw [hTb p hp r hr hpr] at this
  exact Bool.noConfusion this

theorem c5_dich : ∀ x y, x < 5 → y < 5 → x ≠ y →
    V001.c5 x y = true ∨ V001.c5c x y = true := by
  intro x y _ _ hxy
  by_cases h : V001.c5 x y = true
  · exact Or.inl h
  · exact Or.inr (by simp [V001.c5c, hxy, h])

/-! ## The stacked construction -/

-- `a` levels of the 5-cycle over `b` levels of `Pal(17)` over `c` levels of `Pal(37)` over
-- `d` levels of `Pal(101)` over `m` blocks of size `m`, and the same in the other colour.
def mixed (a b c d m : ℕ) : ℕ → ℕ → Bool :=
  lexAdj 5 (lexAdj 17 (lexAdj 37 (lexAdj 101 (V002.blk m) pal d) V005.pal c) V003.pal b)
    V001.c5 a

def mixedc (a b c d m : ℕ) : ℕ → ℕ → Bool :=
  lexAdj 5 (lexAdj 17 (lexAdj 37 (lexAdj 101 (V002.blkc m) palc d) V005.palc c) V003.palc b)
    V001.c5c a

def GM (a b c d m N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := mixed a b c d m x.val y.val = true
  symm := ⟨fun _ _ h => lexAdj_symm 5 (lexAdj_symm 17 (lexAdj_symm 37
    (lexAdj_symm 101 (V002.blk_symm m) pal_symm d) V005.pal_symm c) V003.pal_symm b)
    V001.c5_symm a _ _ h⟩
  loopless := ⟨fun x h => by
    simp only [mixed] at h
    rw [lexAdj_irrefl 5 (lexAdj_irrefl 17 (lexAdj_irrefl 37
      (lexAdj_irrefl 101 (V002.blk_irrefl m) pal_irrefl d) V005.pal_irrefl c) V003.pal_irrefl b)
      V001.c5_irrefl a x.val] at h
    exact Bool.noConfusion h⟩

theorem GM_adj {a b c d m N : ℕ} {x y : Fin N} :
    (GM a b c d m N).Adj x y ↔ mixed a b c d m x.val y.val = true := Iff.rfl

theorem main {a b c d m n : ℕ} (hn2 : 2 ≤ n)
    (h : 2 ^ a * (3 ^ b * (4 ^ c * (5 ^ d * m))) < n) :
    5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * m ^ 2))) + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hNle : N ≤ 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (m * m)))) := by
    have he : 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * m ^ 2))) =
        5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (m * m)))) := by ring
    omega
  have hD := clique_card 101 5 (by norm_num) pal_irrefl pal_key (m * m) m (V002.blk_clique m) d
  have hC := clique_card 37 4 (by norm_num) V005.pal_irrefl V005.pal_key _ _ hD c
  have hB := clique_card 17 3 (by norm_num) V003.pal_irrefl V003.pal_key _ _ hC b
  have hA := clique_card 5 2 (by norm_num) V001.c5_irrefl c5_key _ _ hB a
  have hDc := clique_card 101 5 (by norm_num) palc_irrefl palc_key (m * m) m
    (V002.blkc_clique m) d
  have hCc := clique_card 37 4 (by norm_num) V005.palc_irrefl V005.palc_key _ _ hDc c
  have hBc := clique_card 17 3 (by norm_num) V003.palc_irrefl V003.palc_key _ _ hCc b
  have hAc := clique_card 5 2 (by norm_num) V001.c5c_irrefl c5c_key _ _ hBc a
  have hdich := lexAdj_dichotomy 5 _ (lexAdj_dichotomy 17 _ (lexAdj_dichotomy 37 _
    (lexAdj_dichotomy 101 (m * m) (V002.blk_dichotomy m) pal_dichotomy (by norm_num) d)
    V005.pal_dichotomy (by norm_num) c) V003.pal_dichotomy (by norm_num) b) c5_dich
    (by norm_num) a
  rcases hforces (GM a b c d m N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := hA (S.image (fun z : Fin N => z.val)) ?_ ?_
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
  · have hcard := hAc (T.image (fun z : Fin N => z.val)) ?_ ?_
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
      have hz5 : (z : ℕ) < 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (m * m)))) :=
        lt_of_lt_of_le z.isLt hNle
      have hw5 : (wv : ℕ) < 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (m * m)))) :=
        lt_of_lt_of_le wv.isLt hNle
      rcases hdich z.val wv.val hz5 hw5 hxy with hd | hd
      · exact absurd (GM_adj.mpr hd) hadj.2
      · exact hd

/-! ## The record -/

theorem term_le {n : ℕ} (hn2 : 2 ≤ n) (a b c d : ℕ) :
    5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d)) ^ 2 + 1
      ≤ f n := by
  have hle : (n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) ≤ n - 1 :=
    Nat.div_mul_le_self _ _
  have hmain := main (a := a) (b := b) (c := c) (d := d)
    (m := (n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d)) hn2 (by
    have : 2 ^ a * (3 ^ b * (4 ^ c * (5 ^ d * ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d))))) =
        (n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) := by ring
    omega)
  have he : 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d)) ^ 2)))
      = 5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d)) ^ 2 := by
    ring
  omega

theorem one_le {n : ℕ} (hn2 : 2 ≤ n) : (1 : ℕ) ≤ f n := by
  have := main (a := 0) (b := 0) (c := 0) (d := 0) (m := 0) hn2 (by simpa using by omega)
  simpa using this

theorem goD_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel a b c d,
    goD (n - 1) fuel (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d) + 1
      ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro a b c d; simpa [goD] using one_le hn2
  | succ fuel ih =>
    intro a b c d
    rw [goD]
    by_cases hlt : n - 1 < 2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d
    · simpa [hlt] using one_le hn2
    · rw [if_neg hlt]
      have hnext := ih a b c (d + 1)
      rw [show 2 ^ a * 3 ^ b * 4 ^ c * 5 ^ (d + 1) = 5 * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) from
        by ring, show 5 ^ a * 17 ^ b * 37 ^ c * 101 ^ (d + 1) =
        101 * (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d) from by ring] at hnext
      rcases Nat.le_total
          (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d)) ^ 2)
          (goD (n - 1) fuel (5 * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d))
            (101 * (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d))) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact term_le hn2 a b c d

theorem goC_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel a b c,
    goC (n - 1) fuel (2 ^ a * 3 ^ b * 4 ^ c) (5 ^ a * 17 ^ b * 37 ^ c) + 1 ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro a b c; simpa [goC] using one_le hn2
  | succ fuel ih =>
    intro a b c
    rw [goC]
    by_cases hlt : n - 1 < 2 ^ a * 3 ^ b * 4 ^ c
    · simpa [hlt] using one_le hn2
    · rw [if_neg hlt]
      have hD := goD_le hn2 (fuel + 1) a b c 0
      simp only [pow_zero, Nat.mul_one] at hD
      have hnext := ih a b (c + 1)
      rw [show 2 ^ a * 3 ^ b * 4 ^ (c + 1) = 4 * (2 ^ a * 3 ^ b * 4 ^ c) from by ring,
        show 5 ^ a * 17 ^ b * 37 ^ (c + 1) = 37 * (5 ^ a * 17 ^ b * 37 ^ c) from by ring] at hnext
      rcases Nat.le_total (goD (n - 1) (fuel + 1) (2 ^ a * 3 ^ b * 4 ^ c) (5 ^ a * 17 ^ b * 37 ^ c))
          (goC (n - 1) fuel (4 * (2 ^ a * 3 ^ b * 4 ^ c)) (37 * (5 ^ a * 17 ^ b * 37 ^ c)))
          with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact hD

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
      have hC := goC_le hn2 (fuel + 1) a b 0
      simp only [pow_zero, Nat.mul_one] at hC
      have hnext := ih a (b + 1)
      rw [show 2 ^ a * 3 ^ (b + 1) = 3 * (2 ^ a * 3 ^ b) from by ring,
        show 5 ^ a * 17 ^ (b + 1) = 17 * (5 ^ a * 17 ^ b) from by ring] at hnext
      rcases Nat.le_total (goC (n - 1) (fuel + 1) (2 ^ a * 3 ^ b) (5 ^ a * 17 ^ b))
          (goB (n - 1) fuel (3 * (2 ^ a * 3 ^ b)) (17 * (5 ^ a * 17 ^ b))) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact hC

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
      rw [show 2 ^ (a + 1) = 2 * 2 ^ a from by ring, show 5 ^ (a + 1) = 5 * 5 ^ a from by ring]
        at hnext
      rcases Nat.le_total (goB (n - 1) (fuel + 1) (2 ^ a) (5 ^ a))
          (goA (n - 1) fuel (2 * 2 ^ a) (5 * 5 ^ a)) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact hB

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  have := goA_le hn2 n 0
  simpa using this

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V007.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V007.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V007.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 6) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V008
