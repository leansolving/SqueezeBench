import SqueezeBench.Problems.Ramsey.Records.Lower.V011.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V010.Proof

/-! Record V011 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V011.lean`. V008's mixed lexicographic product gains a fifth base,
the Paley graph on 281 vertices (no `K₈` in either colour; `R(8,8) > 281`,
Burling–Reyner 1972). The residue test is Euler's criterion `z^140 ≡ 1 (mod 281)`, so
that multiplication by a residue is an automorphism by plain modular arithmetic; a `K₈`
through `a` is translated to `0`, one of its other vertices is multiplied to `1`, and the
remaining `K₆` lies in the common neighbourhood of `0` and `1` (69 vertices), where V008's
depth-first checker rules it out. The other colour is carried to the first by multiplying
with the non-residue `3`. All the lexicographic machinery is V008's, generic in the modulus. -/
namespace SqueezeBench.Ramsey.Lower.V011

open SqueezeBench SimpleGraph

/-! ## The Paley graph on 281 vertices, with Euler's criterion as the residue test -/

-- `z` is a nonzero square mod 281 iff `z^140 ≡ 1 (mod 281)`.
def qr (z : ℕ) : Bool := z ^ 140 % 281 == 1

def pal (x y : ℕ) : Bool := qr ((y % 281 + 281 - x % 281) % 281)

def palc (x y : ℕ) : Bool := !(x % 281 == y % 281) && !(pal x y)

-- The common neighbourhood of `0` and `1`.
def tList : List ℕ :=
  [2, 5, 8, 9, 10, 17, 18, 29, 32, 33, 34, 35, 36, 40, 50, 57, 58, 59, 63, 64, 69, 70, 79, 80,
   81, 86, 101, 112, 119, 124, 125, 126, 137, 138, 141, 144, 145, 156, 157, 158, 163, 170, 181,
   196, 201, 202, 203, 212, 213, 218, 219, 223, 224, 225, 232, 242, 246, 247, 248, 249, 250,
   253, 264, 265, 272, 273, 274, 277, 280]

theorem qr_zero : qr 0 = false := by decide

-- `−1` is a residue: the residues are closed under negation.
theorem qr_neg_fin : ∀ d : Fin 281, qr ((281 - (d : ℕ)) % 281) = qr d := by decide +kernel

-- `3` is a non-residue: multiplying by it swaps residues and non-residues.
theorem qr_three_fin : ∀ d : Fin 281, (d : ℕ) ≠ 0 → qr (3 * (d : ℕ) % 281) = !(qr d) := by
  decide +kernel

-- A residue has a residue inverse (Fermat: `p^279` inverts `p`).
theorem inv_fin : ∀ p : Fin 281, qr p = true →
    (p : ℕ) * ((p : ℕ) ^ 279 % 281) % 281 = 1 ∧ qr ((p : ℕ) ^ 279 % 281) = true := by
  decide +kernel

theorem tmem_fin : ∀ z : Fin 281, qr z = true → qr (((z : ℕ) + 281 - 1) % 281) = true →
    (z : ℕ) ∈ tList := by
  decide +kernel

-- The common neighbourhood of `0` and `1` carries no `K₆`.
theorem t_k6_free : V008.cliqueFree pal 80 6 tList = true := by decide +kernel

-- Multiplying by a residue preserves residues: Euler's criterion is multiplicative.
theorem qr_mul {u : ℕ} (hu : qr u = true) (z : ℕ) : qr (u * z % 281) = qr z := by
  have hu' : u ^ 140 % 281 = 1 := by simpa [qr] using hu
  have h : (u * z % 281) ^ 140 % 281 = z ^ 140 % 281 := by
    rw [← Nat.pow_mod, Nat.mul_pow, Nat.mul_mod, hu', Nat.one_mul, Nat.mod_mod]
  simp only [qr, h]

-- `u·y − u·x ≡ u·(y − x)` mod 281, with natural subtraction.
theorem mul_diff {u x y : ℕ} (hx : x < 281) (hy : y < 281) :
    (u * y % 281 + 281 - u * x % 281) % 281 = u * ((y + 281 - x) % 281) % 281 := by
  have h1 : u * x % 281 ≤ u * y % 281 + 281 := by
    have := Nat.mod_lt (u * x) (by norm_num : 281 > 0); omega
  have h2 : x ≤ y + 281 := by omega
  have key : (((u * y % 281 + 281 - u * x % 281) % 281 : ℕ) : ZMod 281) =
      ((u * ((y + 281 - x) % 281) % 281 : ℕ) : ZMod 281) := by
    simp only [ZMod.natCast_mod, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self]
    ring
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp key
  rwa [Nat.mod_mod, Nat.mod_mod] at this

theorem pal_irrefl : ∀ a, pal a a = false := by
  intro a
  simp only [pal]
  rw [show (a % 281 + 281 - a % 281) % 281 = 0 from by omega]
  exact qr_zero

theorem palc_irrefl : ∀ a, palc a a = false := by
  intro a; simp [palc]

theorem pal_symm : ∀ p q, pal p q = true → pal q p = true := by
  intro p q h
  simp only [pal] at h ⊢
  rw [show (p % 281 + 281 - q % 281) % 281 = (281 - (q % 281 + 281 - p % 281) % 281) % 281 from
    by omega]
  have := qr_neg_fin ⟨(q % 281 + 281 - p % 281) % 281, Nat.mod_lt _ (by norm_num)⟩
  simp only at this
  rw [this]
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

theorem pal_dichotomy : ∀ x y, x < 281 → y < 281 → x ≠ y →
    pal x y = true ∨ palc x y = true := by
  intro x y hx hy hxy
  by_cases h : pal x y = true
  · exact Or.inl h
  · refine Or.inr ?_
    simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    exact ⟨by omega, Bool.not_eq_true _ |>.mp h⟩

-- Translation is an automorphism.
theorem pal_translate {a x y : ℕ} (ha : a < 281) (hx : x < 281) (hy : y < 281) :
    pal ((x + 281 - a) % 281) ((y + 281 - a) % 281) = pal x y := by
  simp only [pal, Nat.mod_mod]
  congr 1
  omega

-- Multiplication by a residue is an automorphism.
theorem pal_mul {u x y : ℕ} (hu : qr u = true) (hx : x < 281) (hy : y < 281) :
    pal (u * x % 281) (u * y % 281) = pal x y := by
  simp only [pal, Nat.mod_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rw [mul_diff hx hy, qr_mul hu]

theorem qr_of_pal {a x : ℕ} (ha : a < 281) (hx : x < 281) (h : pal a x = true) :
    qr ((x + 281 - a) % 281) = true := by
  simpa only [pal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hx] using h

-- No `K₈` in the Paley graph: through `a`, translate to `0`, then multiply the resulting
-- `K₇` inside the residues so that one of its vertices becomes `1`; the remaining `K₆` lies
-- in the common neighbourhood of `0` and `1`, which the checker rules out.
theorem pal_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 281) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → pal x y = true) → T.card ≤ 7 := by
  intro T hT hadj
  by_contra hc
  obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have haL : a < 281 := hT a ha
  have hinj1 : Set.InjOn (fun x => (x + 281 - a) % 281) ↑(T.erase a) := by
    intro x hx y hy hxy
    have hxL := hT x (Finset.mem_of_mem_erase hx)
    have hyL := hT y (Finset.mem_of_mem_erase hy)
    simp only at hxy
    omega
  have hT1card : ((T.erase a).image (fun x => (x + 281 - a) % 281)).card = T.card - 1 := by
    rw [Finset.card_image_of_injOn hinj1, Finset.card_erase_of_mem ha]
  have hT1L : ∀ z ∈ (T.erase a).image (fun x => (x + 281 - a) % 281), z < 281 := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact Nat.mod_lt _ (by norm_num)
  have hT1qr : ∀ z ∈ (T.erase a).image (fun x => (x + 281 - a) % 281), qr z = true := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact qr_of_pal haL (hT x (Finset.mem_of_mem_erase hx))
      (hadj a ha x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm)
  have hT1adj : ∀ z ∈ (T.erase a).image (fun x => (x + 281 - a) % 281),
      ∀ w ∈ (T.erase a).image (fun x => (x + 281 - a) % 281), z ≠ w → pal z w = true := by
    intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by rintro rfl; exact hzw rfl
    rw [pal_translate haL (hT x (Finset.mem_of_mem_erase hx)) (hT y (Finset.mem_of_mem_erase hy))]
    exact hadj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
  obtain ⟨p, hp⟩ : ((T.erase a).image (fun x => (x + 281 - a) % 281)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hpL := hT1L p hp
  obtain ⟨hpu, hu⟩ := inv_fin ⟨p, hpL⟩ (hT1qr p hp)
  simp only at hpu hu
  have hinj2 : Set.InjOn (fun x => p ^ 279 % 281 * x % 281)
      ↑(((T.erase a).image (fun x => (x + 281 - a) % 281)).erase p) := by
    intro x hx y hy hxy
    have hxL := hT1L x (Finset.mem_of_mem_erase hx)
    have hyL := hT1L y (Finset.mem_of_mem_erase hy)
    simp only at hxy
    have key : ∀ z, (p * (p ^ 279 % 281) * z) % 281 = z % 281 := by
      intro z
      rw [Nat.mul_mod, hpu, Nat.one_mul, Nat.mod_mod]
    have h1 : (p * (p ^ 279 % 281) * x) % 281 = (p * (p ^ 279 % 281) * y) % 281 := by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_mod, hxy, ← Nat.mul_mod]
    rw [key, key, Nat.mod_eq_of_lt hxL, Nat.mod_eq_of_lt hyL] at h1
    exact h1
  have hT2card : ((((T.erase a).image (fun x => (x + 281 - a) % 281)).erase p).image
      (fun x => p ^ 279 % 281 * x % 281)).card = T.card - 2 := by
    rw [Finset.card_image_of_injOn hinj2, Finset.card_erase_of_mem hp, hT1card]
    omega
  have hcard := V008.cliqueFree_sound pal 80 6 tList t_k6_free
    ((((T.erase a).image (fun x => (x + 281 - a) % 281)).erase p).image
      (fun x => p ^ 279 % 281 * x % 281)) ?_ ?_
  · omega
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxL := hT1L x (Finset.mem_of_mem_erase hx)
    refine tmem_fin ⟨p ^ 279 % 281 * x % 281, Nat.mod_lt _ (by norm_num)⟩ ?_ ?_
    · simp only
      rw [qr_mul hu]
      exact hT1qr x (Finset.mem_of_mem_erase hx)
    · simp only
      have hpx := hT1adj p hp x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm
      rw [show p ^ 279 % 281 * x % 281 + 281 - 1 = p ^ 279 % 281 * x % 281 + 281 -
        p ^ 279 % 281 * p % 281 from by rw [Nat.mul_comm (p ^ 279 % 281) p, hpu],
        mul_diff hpL hxL, qr_mul hu]
      exact qr_of_pal hpL hxL hpx
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by rintro rfl; exact hzw rfl
    rw [pal_mul hu (hT1L x (Finset.mem_of_mem_erase hx)) (hT1L y (Finset.mem_of_mem_erase hy))]
    exact hT1adj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy

-- The complement: multiplying by the non-residue `3` turns its cliques into cliques of `pal`.
theorem palc_key : ∀ T : Finset ℕ, (∀ x ∈ T, x < 281) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → palc x y = true) → T.card ≤ 7 := by
  intro T hT hadj
  have hinj : Set.InjOn (fun x => 3 * x % 281) ↑T := by
    intro x hx y hy hxy
    have := hT x hx
    have := hT y hy
    simp only at hxy
    omega
  have := pal_key (T.image (fun x => 3 * x % 281)) ?_ ?_
  · rwa [Finset.card_image_of_injOn hinj] at this
  · intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact Nat.mod_lt _ (by norm_num)
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by rintro rfl; exact hzw rfl
    have hxL := hT x hx
    have hyL := hT y hy
    have h := hadj x hx y hy hxy
    simp only [palc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
    have hfalse : qr ((y + 281 - x) % 281) = false := by
      simpa only [pal, Nat.mod_eq_of_lt hxL, Nat.mod_eq_of_lt hyL] using h.2
    have hne : (y + 281 - x) % 281 ≠ 0 := by omega
    simp only [pal, Nat.mod_mod]
    rw [show (3 * y % 281 + 281 - 3 * x % 281) % 281 = 3 * ((y + 281 - x) % 281) % 281 from
      by omega]
    have := qr_three_fin ⟨(y + 281 - x) % 281, Nat.mod_lt _ (by norm_num)⟩ hne
    simp only at this
    rw [this, hfalse]
    rfl


/-! ## The stacked construction with five bases -/

-- `a` levels of the 5-cycle over `b` of `Pal(17)` over `c` of `Pal(37)` over `d` of `Pal(101)`
-- over `e` of `Pal(281)` over `m` blocks of size `m`, and the same in the other colour.
def mixed (a b c d e m : ℕ) : ℕ → ℕ → Bool :=
  V008.lexAdj 5 (V008.lexAdj 17 (V008.lexAdj 37 (V008.lexAdj 101
    (V008.lexAdj 281 (V002.blk m) pal e) V008.pal d) V005.pal c) V003.pal b) V001.c5 a

def mixedc (a b c d e m : ℕ) : ℕ → ℕ → Bool :=
  V008.lexAdj 5 (V008.lexAdj 17 (V008.lexAdj 37 (V008.lexAdj 101
    (V008.lexAdj 281 (V002.blkc m) palc e) V008.palc d) V005.palc c) V003.palc b) V001.c5c a

def GM (a b c d e m N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := mixed a b c d e m x.val y.val = true
  symm := ⟨fun _ _ h => V008.lexAdj_symm 5 (V008.lexAdj_symm 17 (V008.lexAdj_symm 37
    (V008.lexAdj_symm 101 (V008.lexAdj_symm 281 (V002.blk_symm m) pal_symm e) V008.pal_symm d)
    V005.pal_symm c) V003.pal_symm b) V001.c5_symm a _ _ h⟩
  loopless := ⟨fun x h => by
    simp only [mixed] at h
    rw [V008.lexAdj_irrefl 5 (V008.lexAdj_irrefl 17 (V008.lexAdj_irrefl 37
      (V008.lexAdj_irrefl 101 (V008.lexAdj_irrefl 281 (V002.blk_irrefl m) pal_irrefl e)
      V008.pal_irrefl d) V005.pal_irrefl c) V003.pal_irrefl b) V001.c5_irrefl a x.val] at h
    exact Bool.noConfusion h⟩

theorem GM_adj {a b c d e m N : ℕ} {x y : Fin N} :
    (GM a b c d e m N).Adj x y ↔ mixed a b c d e m x.val y.val = true := Iff.rfl

theorem main {a b c d e m n : ℕ} (hn2 : 2 ≤ n)
    (h : 2 ^ a * (3 ^ b * (4 ^ c * (5 ^ d * (7 ^ e * m)))) < n) :
    5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e * m ^ 2)))) + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hNle : N ≤ 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e * (m * m))))) := by
    have he : 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e * m ^ 2)))) =
        5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e * (m * m))))) := by ring
    omega
  have hE := V008.clique_card 281 7 (by norm_num) pal_irrefl pal_key (m * m) m
    (V002.blk_clique m) e
  have hD := V008.clique_card 101 5 (by norm_num) V008.pal_irrefl V008.pal_key _ _ hE d
  have hC := V008.clique_card 37 4 (by norm_num) V005.pal_irrefl V005.pal_key _ _ hD c
  have hB := V008.clique_card 17 3 (by norm_num) V003.pal_irrefl V003.pal_key _ _ hC b
  have hA := V008.clique_card 5 2 (by norm_num) V001.c5_irrefl V008.c5_key _ _ hB a
  have hEc := V008.clique_card 281 7 (by norm_num) palc_irrefl palc_key (m * m) m
    (V002.blkc_clique m) e
  have hDc := V008.clique_card 101 5 (by norm_num) V008.palc_irrefl V008.palc_key _ _ hEc d
  have hCc := V008.clique_card 37 4 (by norm_num) V005.palc_irrefl V005.palc_key _ _ hDc c
  have hBc := V008.clique_card 17 3 (by norm_num) V003.palc_irrefl V003.palc_key _ _ hCc b
  have hAc := V008.clique_card 5 2 (by norm_num) V001.c5c_irrefl V008.c5c_key _ _ hBc a
  have hdich := V008.lexAdj_dichotomy 5 _ (V008.lexAdj_dichotomy 17 _
    (V008.lexAdj_dichotomy 37 _ (V008.lexAdj_dichotomy 101 _
    (V008.lexAdj_dichotomy 281 (m * m) (V002.blk_dichotomy m) pal_dichotomy (by norm_num) e)
    V008.pal_dichotomy (by norm_num) d) V005.pal_dichotomy (by norm_num) c)
    V003.pal_dichotomy (by norm_num) b) V008.c5_dich (by norm_num) a
  rcases hforces (GM a b c d e m N) with ⟨S, hS⟩ | ⟨T, hT⟩
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
      have hz5 : (z : ℕ) < 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e * (m * m))))) :=
        lt_of_lt_of_le z.isLt hNle
      have hw5 : (wv : ℕ) < 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e * (m * m))))) :=
        lt_of_lt_of_le wv.isLt hNle
      rcases hdich z.val wv.val hz5 hw5 hxy with hd | hd
      · exact absurd (GM_adj.mpr hd) hadj.2
      · exact hd

/-! ## The record -/

theorem term_le {n : ℕ} (hn2 : 2 ≤ n) (a b c d e : ℕ) :
    5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ e *
      ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)) ^ 2 + 1 ≤ f n := by
  have hle : (n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e) *
      (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e) ≤ n - 1 := Nat.div_mul_le_self _ _
  have hmain := main (a := a) (b := b) (c := c) (d := d) (e := e)
    (m := (n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)) hn2 (by
    have : 2 ^ a * (3 ^ b * (4 ^ c * (5 ^ d * (7 ^ e *
        ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)))))) =
        (n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e) *
          (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e) := by ring
    omega)
  have he : 5 ^ a * (17 ^ b * (37 ^ c * (101 ^ d * (281 ^ e *
      ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)) ^ 2)))) =
      5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ e *
        ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)) ^ 2 := by
    ring
  omega

theorem one_le {n : ℕ} (hn2 : 2 ≤ n) : (1 : ℕ) ≤ f n := by
  have := main (a := 0) (b := 0) (c := 0) (d := 0) (e := 0) (m := 0) hn2 (by simpa using by omega)
  simpa using this

theorem goE_le {n : ℕ} (hn2 : 2 ≤ n) : ∀ fuel a b c d e,
    goE (n - 1) fuel (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)
      (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ e) + 1 ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro a b c d e; simpa [goE] using one_le hn2
  | succ fuel ih =>
    intro a b c d e
    rw [goE]
    by_cases hlt : n - 1 < 2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e
    · simpa [hlt] using one_le hn2
    · rw [if_neg hlt]
      have hnext := ih a b c d (e + 1)
      rw [show 2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ (e + 1) =
          7 * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e) from by ring,
        show 5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ (e + 1) =
          281 * (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ e) from by ring] at hnext
      rcases Nat.le_total
          (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ e *
            ((n - 1) / (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e)) ^ 2)
          (goE (n - 1) fuel (7 * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d * 7 ^ e))
            (281 * (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d * 281 ^ e))) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact term_le hn2 a b c d e

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
      have hE := goE_le hn2 (fuel + 1) a b c d 0
      simp only [pow_zero, Nat.mul_one] at hE
      have hnext := ih a b c (d + 1)
      rw [show 2 ^ a * 3 ^ b * 4 ^ c * 5 ^ (d + 1) = 5 * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) from
        by ring, show 5 ^ a * 17 ^ b * 37 ^ c * 101 ^ (d + 1) =
        101 * (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d) from by ring] at hnext
      rcases Nat.le_total
          (goE (n - 1) (fuel + 1) (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d)
            (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d))
          (goD (n - 1) fuel (5 * (2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d))
            (101 * (5 ^ a * 17 ^ b * 37 ^ c * 101 ^ d))) with h | h
      · rw [Nat.max_eq_right h]; exact hnext
      · rw [Nat.max_eq_left h]; exact hE

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
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V010.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V010.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V010.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 8) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V011
