import SqueezeBench.Problems.CapSet.Records.Lower.V005.Def
import SqueezeBench.Problems.CapSet.Records.Lower.V004.Proof

/-! Record V005 for CapSet, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/CapSet/Lower/V005.lean`. -/

namespace SqueezeBench.CapSet.Lower.V005

open SqueezeBench SqueezeBench.CapSet Finset

-- ## Caps in an additive group, extendable collections, admissible sets (Tyrrell 2023, §2).

section General

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

-- A cap: `x + y + z = 0` only when `x = y`.
def IsCap (A : Finset G) : Prop := ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y

-- Tyrrell's Definition 2.4.
structure Extendable (A : Fin 3 → Finset G) : Prop where
  cap : ∀ i, IsCap (A i)
  e1 : ∀ x ∈ A 0, ∀ y ∈ A 0, ∀ z ∈ A 1 ∪ A 2, x + y + z ≠ 0
  e2 : ∀ x ∈ A 0, ∀ y ∈ A 1, ∀ z ∈ A 2, x + y + z ≠ 0

-- The label patterns `{0,0,1}`, `{0,0,2}` and `{0,1,2}`, as multisets.
def Good (a b c : Fin 3) : Prop :=
  (a = 0 ∧ b = 0 ∧ c ≠ 0) ∨ (a = 0 ∧ c = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ c = 0 ∧ a ≠ 0) ∨
    (a ≠ b ∧ b ≠ c ∧ a ≠ c)

-- Tyrrell's Definition 2.5 (the second half of the pair condition is the first with `s, t` swapped).
structure Admissible {m : ℕ} (S : Finset (Fin m → Fin 3)) : Prop where
  pair : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ i, s i = 0 ∧ t i ≠ 0
  triple : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, s ≠ t → t ≠ u → s ≠ u → ∃ k, Good (s k) (t k) (u k)

-- The product `A (s 0) × ⋯ × A (s (m-1))`, and the union of the products over `S`.
def piece {m : ℕ} (A : Fin 3 → Finset G) (s : Fin m → Fin 3) : Finset (Fin m → G) :=
  Fintype.piFinset fun j => A (s j)

def ext {m : ℕ} (A : Fin 3 → Finset G) (S : Finset (Fin m → Fin 3)) : Finset (Fin m → G) :=
  S.biUnion (piece A)

omit [AddCommGroup G] [DecidableEq G] in
theorem mem_piece {m : ℕ} {A : Fin 3 → Finset G} {s : Fin m → Fin 3} {x : Fin m → G} :
    x ∈ piece A s ↔ ∀ j, x j ∈ A (s j) := Fintype.mem_piFinset

omit [AddCommGroup G] in
theorem mem_ext {m : ℕ} {A : Fin 3 → Finset G} {S : Finset (Fin m → Fin 3)} {x : Fin m → G} :
    x ∈ ext A S ↔ ∃ s ∈ S, ∀ j, x j ∈ A (s j) := by
  simp only [ext, Finset.mem_biUnion, mem_piece]

omit [AddCommGroup G] [DecidableEq G] in
theorem mem_of_eq {A : Fin 3 → Finset G} {v : Fin 3} {w : G} (h : w ∈ A v) (hv : v = 0) :
    w ∈ A 0 := hv ▸ h

omit [AddCommGroup G] in
theorem mem_union_of_ne {A : Fin 3 → Finset G} {v : Fin 3} (hv : v ≠ 0) {w : G}
    (hw : w ∈ A v) : w ∈ A 1 ∪ A 2 := by
  rw [Finset.mem_union]
  fin_cases v
  · exact absurd rfl hv
  · exact Or.inl hw
  · exact Or.inr hw

theorem Extendable.e1' {A : Fin 3 → Finset G} (hA : Extendable A) {x y z : G}
    (hx : x ∈ A 0) (hy : y ∈ A 0) {v : Fin 3} (hv : v ≠ 0) (hz : z ∈ A v) :
    x + y + z ≠ 0 :=
  hA.e1 x hx y hy z (mem_union_of_ne hv hz)

theorem Extendable.e2' {A : Fin 3 → Finset G} (hA : Extendable A) {a b c : Fin 3}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {x y z : G}
    (hx : x ∈ A a) (hy : y ∈ A b) (hz : z ∈ A c) : x + y + z ≠ 0 := by
  intro h
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals first
    | exact absurd rfl hab
    | exact absurd rfl hbc
    | exact absurd rfl hac
    | exact hA.e2 _ hx _ hy _ hz h
    | exact hA.e2 _ hx _ hz _ hy (by rw [← h]; abel)
    | exact hA.e2 _ hy _ hx _ hz (by rw [← h]; abel)
    | exact hA.e2 _ hy _ hz _ hx (by rw [← h]; abel)
    | exact hA.e2 _ hz _ hx _ hy (by rw [← h]; abel)
    | exact hA.e2 _ hz _ hy _ hx (by rw [← h]; abel)

-- Tyrrell's Lemma 2.7: the extended product over an admissible set is a cap.
theorem isCap_ext {m : ℕ} {A : Fin 3 → Finset G} {S : Finset (Fin m → Fin 3)}
    (hA : Extendable A) (hS : Admissible S) : IsCap (ext A S) := by
  intro x hx y hy z hz hsum
  obtain ⟨s, hs, hxs⟩ := mem_ext.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_ext.mp hy
  obtain ⟨u, hu, hzu⟩ := mem_ext.mp hz
  have hj : ∀ j, x j + y j + z j = 0 := fun j => by
    have := congrFun hsum j
    simpa using this
  by_cases hst : s = t
  · subst hst
    by_cases hsu : s = u
    · subst hsu
      funext j
      exact hA.cap (s j) (x j) (hxs j) (y j) (hyt j) (z j) (hzu j) (hj j)
    · obtain ⟨i, hi1, hi2⟩ := hS.pair s hs u hu hsu
      exact absurd (hj i) (hA.e1' (mem_of_eq (hxs i) hi1) (mem_of_eq (hyt i) hi1) hi2 (hzu i))
  · by_cases htu : t = u
    · subst htu
      obtain ⟨i, hi1, hi2⟩ := hS.pair t ht s hs (Ne.symm hst)
      exact absurd (show y i + z i + x i = 0 by rw [← hj i]; abel)
        (hA.e1' (mem_of_eq (hyt i) hi1) (mem_of_eq (hzu i) hi1) hi2 (hxs i))
    · by_cases hsu : s = u
      · subst hsu
        obtain ⟨i, hi1, hi2⟩ := hS.pair s hs t ht hst
        exact absurd (show x i + z i + y i = 0 by rw [← hj i]; abel)
          (hA.e1' (mem_of_eq (hxs i) hi1) (mem_of_eq (hzu i) hi1) hi2 (hyt i))
      · obtain ⟨k, hk⟩ := hS.triple s hs t ht u hu hst htu hsu
        rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact absurd (hj k) (hA.e1' (mem_of_eq (hxs k) h1) (mem_of_eq (hyt k) h2) h3 (hzu k))
        · exact absurd (show x k + z k + y k = 0 by rw [← hj k]; abel)
            (hA.e1' (mem_of_eq (hxs k) h1) (mem_of_eq (hzu k) h2) h3 (hyt k))
        · exact absurd (show y k + z k + x k = 0 by rw [← hj k]; abel)
            (hA.e1' (mem_of_eq (hyt k) h1) (mem_of_eq (hzu k) h2) h3 (hxs k))
        · exact absurd (hj k) (hA.e2' h1 h2 h3 (hxs k) (hyt k) (hzu k))

-- The products over distinct labels are disjoint (in characteristic 3), so the sizes add up.
theorem card_ext {m : ℕ} {A : Fin 3 → Finset G} {S : Finset (Fin m → Fin 3)}
    (hA : Extendable A) (hS : Admissible S) (h3 : ∀ w : G, w + w + w = 0) :
    (ext A S).card = ∑ s ∈ S, ∏ j, (A (s j)).card := by
  rw [ext, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun s _ => Fintype.card_piFinset _
  · intro s hs t ht hst
    show Disjoint (piece A s) (piece A t)
    rw [Finset.disjoint_left]
    intro x hxs hxt
    obtain ⟨i, hi1, hi2⟩ := hS.pair s hs t ht hst
    exact hA.e1' (mem_of_eq (mem_piece.mp hxs i) hi1) (mem_of_eq (mem_piece.mp hxs i) hi1) hi2
      (mem_piece.mp hxt i) (h3 _)

-- Caps are carried along injective additive maps.
omit [DecidableEq G] in
theorem IsCap.map {H : Type*} [AddCommGroup H] [DecidableEq H] {A : Finset G} (hA : IsCap A)
    (φ : G →+ H) (hφ : Function.Injective φ) : IsCap (A.map ⟨φ, hφ⟩) := by
  intro x hx y hy z hz h
  rw [Finset.mem_map] at hx hy hz
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  obtain ⟨z, hz, rfl⟩ := hz
  simp only [Function.Embedding.coeFn_mk] at h ⊢
  rw [← map_add, ← map_add, ← map_zero φ] at h
  rw [hA x hx y hy z hz (hφ h)]

end General

-- ## Points of `F₃ⁿ`: caps against `ThreeAPFree`, and the flattening `(Fin m → F₃ᵈ) → F₃^(m d)`.

theorem three_add {n : ℕ} (w : Fin n → ZMod 3) : w + w + w = 0 := by
  funext i
  have : ∀ a : ZMod 3, a + a + a = 0 := by decide
  simpa using this (w i)

theorem neg_eq_add_self {n : ℕ} (w : Fin n → ZMod 3) : -w = w + w := by
  funext i
  have : ∀ a : ZMod 3, -a = a + a := by decide
  simpa using this (w i)

theorem threeAPFree_of_isCap {n : ℕ} {A : Finset (Fin n → ZMod 3)} (hA : IsCap A) :
    ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  intro x hx y hy z hz h
  refine hA x hx y hy z hz ?_
  calc x + y + z = (x + z) + y := by abel
    _ = y + y + y := by rw [h]
    _ = 0 := three_add y

theorem isCap_of_threeAPFree {n : ℕ} {A : Finset (Fin n → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) : IsCap A := by
  intro x hx y hy z hz h
  refine hA hx hy hz ?_
  have h' : (x + z) + y = 0 := by rw [← h]; abel
  rw [eq_neg_of_add_eq_zero_left h', neg_eq_add_self]

theorem card_le_f {n : ℕ} (hn : 1 ≤ n) {A : Finset (Fin n → ZMod 3)} (hA : IsCap A) :
    A.card ≤ SqueezeBench.CapSet.f n :=
  SqueezeBench.CapSet.le_f_of_threeAPFree (by simpa using hn) (threeAPFree_of_isCap hA)

def flat (m d : ℕ) (x : Fin m → Fin d → ZMod 3) : Fin (m * d) → ZMod 3 :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def flatHom (m d : ℕ) : (Fin m → Fin d → ZMod 3) →+ (Fin (m * d) → ZMod 3) :=
  { toFun := flat m d, map_zero' := rfl, map_add' := fun _ _ => rfl }

theorem flat_injective (m d : ℕ) : Function.Injective (flatHom m d) := by
  intro x y h
  funext a b
  have := congrFun h (finProdFinEquiv (a, b))
  simpa [flatHom, flat] using this

-- Sum-freeness of three code lists from a mask identity: no `-(x + y)`, `y ∈ B`, lies in `C`.
theorem no_sum_of_mask {n : ℕ} {B C : List ℕ} {MB MC x : ℕ}
    (hltB : ∀ c ∈ B, c < 3 ^ n) (hltC : ∀ c ∈ C, c < 3 ^ n)
    (hmemB : ∀ c ∈ B, MB.testBit c = true) (hmemC : ∀ c ∈ C, MC.testBit c = true)
    (h : MC &&& V003.refl n x MB = 0) :
    ∀ y ∈ B, ∀ z ∈ C, V003.dec n x + V003.dec n y + V003.dec n z ≠ 0 := by
  intro y hy z hz hsum
  have hz' : V003.dec n z = V003.dec n (V003.thd x y n) := by
    rw [V003.dec_thd]
    exact eq_neg_of_add_eq_zero_right hsum
  have hzy : z = V003.thd x y n := V003.dec_inj (hltC z hz) (V003.thd_lt _ _ _) hz'
  have hp := congrArg (fun m => m.testBit z) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at hp
  rw [hmemC z hz, V003.testBit_refl (hltC z hz), hzy, V003.thd_thd (hltB y hy), hmemB y hy] at hp
  simp at hp

theorem card_of_codes {n : ℕ} {codes : List ℕ} (hlt : ∀ c ∈ codes, c < 3 ^ n)
    (hchain : List.IsChain (· < ·) codes) :
    (codes.map (V003.dec n)).toFinset.card = codes.length := by
  rw [List.toFinset_card_of_nodup (List.Nodup.map_on
    (fun x hx y hy h => V003.dec_inj (hlt x hx) (hlt y hy) h)
    (hchain.pairwise.imp fun h => Nat.ne_of_lt h)), List.length_map]

-- ## The extendable collection `(A₀, A₁, A₂)` of sizes `(12, 112, 112)` in `F₃⁶` (Tyrrell 2023,
-- Lemma 2.14, after Edel 2004): `A₀` = the weight-1 vectors; `A₁ = D ∪ R`, `A₂ = D' ∪ R`, where
-- `D` (`D'`) = the weight-3 vectors supported on a block (a non-block) of the 2-(6,3,2) design
-- `{123,124,135,146,156,236,245,256,345,346}` and `R` = the weight-6 vectors with an even number
-- of ones. Base-3 codes, increasing, with membership masks.

def codes0 : List ℕ := [
    1, 2, 3, 6, 9, 18, 27, 54, 81, 162, 243, 486
  ]

def mask0 : ℕ := 199791907220223502808422222706762643567910281130558153654986045416023791298599776205926665232729872006178821042001567855055370825236622150667076174

theorem codes0_lt : ∀ c ∈ codes0, c < 3 ^ 6 := by decide +kernel

theorem codes0_mem : ∀ c ∈ codes0, mask0.testBit c = true := by decide +kernel

theorem codes0_pair : ∀ x ∈ codes0, mask0 &&& V003.refl 6 x mask0 = 1 <<< x := by
  decide +kernel

theorem codes0_chain : List.IsChain (· < ·) codes0 := by decide +kernel

def codes1 : List ℕ := [
    13, 14, 16, 17, 22, 23, 25, 26, 31, 32, 34, 35, 58, 59, 61, 62, 91, 92, 100, 101, 111, 114,
    117, 126, 138, 141, 144, 153, 172, 173, 181, 182, 192, 195, 198, 207, 219, 222, 225, 234,
    255, 258, 264, 267, 271, 272, 279, 288, 298, 299, 306, 315, 325, 326, 327, 330, 364, 368,
    374, 376, 392, 394, 400, 404, 406, 407, 408, 411, 446, 448, 454, 458, 472, 476, 482, 484,
    498, 501, 507, 510, 514, 515, 522, 531, 541, 542, 549, 558, 568, 569, 570, 573, 608, 610,
    616, 620, 634, 638, 644, 646, 649, 650, 651, 654, 688, 692, 698, 700, 716, 718, 724, 728
  ]

def mask1 : ℕ := 1501981063492961411952637445447124447754428995474048756391141281132566834771754234672320410453904927893965483302964397750490341890341595995365955859177605172773525863330701837985157925227981851649532767068699542662897664

theorem codes1_lt : ∀ c ∈ codes1, c < 3 ^ 6 := by decide +kernel

theorem codes1_mem : ∀ c ∈ codes1, mask1.testBit c = true := by decide +kernel

theorem codes1_pair : ∀ x ∈ codes1, mask1 &&& V003.refl 6 x mask1 = 1 <<< x := by
  decide +kernel

theorem codes1_chain : List.IsChain (· < ·) codes1 := by decide +kernel

def codes2 : List ℕ := [
    37, 38, 39, 42, 46, 47, 48, 51, 64, 65, 66, 69, 73, 74, 75, 78, 85, 86, 88, 89, 93, 96,
    102, 105, 109, 110, 136, 137, 166, 167, 169, 170, 174, 177, 183, 186, 190, 191, 217, 218,
    247, 248, 250, 251, 253, 254, 262, 263, 273, 276, 300, 303, 333, 342, 351, 364, 368, 374,
    376, 378, 392, 394, 400, 404, 414, 423, 432, 446, 448, 454, 458, 459, 472, 476, 482, 484,
    490, 491, 493, 494, 496, 497, 505, 506, 516, 519, 543, 546, 576, 585, 594, 608, 610, 616,
    620, 621, 634, 638, 644, 646, 657, 666, 675, 688, 692, 698, 700, 702, 716, 718, 724, 728
  ]

def mask2 : ℕ := 1501981084533505175217084527764514862457908334281281978330789114100828575116089702802548647190797042903687312349530444905079141139592006901433128258112931266913022839248815358570131191686767419568136348834967530242048000

theorem codes2_lt : ∀ c ∈ codes2, c < 3 ^ 6 := by decide +kernel

theorem codes2_mem : ∀ c ∈ codes2, mask2.testBit c = true := by decide +kernel

theorem codes2_pair : ∀ x ∈ codes2, mask2 &&& V003.refl 6 x mask2 = 1 <<< x := by
  decide +kernel

theorem codes2_chain : List.IsChain (· < ·) codes2 := by decide +kernel

-- E1 and E2 by masks: `-(x + y) ∉ A₁ ∪ A₂` for `x, y ∈ A₀`, and `-(x + y) ∉ A₂` for `x ∈ A₀`, `y ∈ A₁`.
theorem e1_mask : ∀ x ∈ codes0,
    mask1 &&& V003.refl 6 x mask0 = 0 ∧ mask2 &&& V003.refl 6 x mask0 = 0 := by decide +kernel

theorem e2_mask : ∀ x ∈ codes0, mask2 &&& V003.refl 6 x mask1 = 0 := by decide +kernel

def A0 : Finset (Fin 6 → ZMod 3) := (codes0.map (V003.dec 6)).toFinset
def A1 : Finset (Fin 6 → ZMod 3) := (codes1.map (V003.dec 6)).toFinset
def A2 : Finset (Fin 6 → ZMod 3) := (codes2.map (V003.dec 6)).toFinset
def A6 : Fin 3 → Finset (Fin 6 → ZMod 3) := ![A0, A1, A2]

theorem A0_card : A0.card = 12 := by
  rw [A0, card_of_codes codes0_lt codes0_chain]; decide +kernel
theorem A1_card : A1.card = 112 := by
  rw [A1, card_of_codes codes1_lt codes1_chain]; decide +kernel
theorem A2_card : A2.card = 112 := by
  rw [A2, card_of_codes codes2_lt codes2_chain]; decide +kernel

theorem A6_ext : Extendable A6 where
  cap i := by
    fin_cases i
    · exact isCap_of_threeAPFree
        (V003.threeAPFree_of_mask 6 codes0 mask0 codes0_lt codes0_mem codes0_pair)
    · exact isCap_of_threeAPFree
        (V003.threeAPFree_of_mask 6 codes1 mask1 codes1_lt codes1_mem codes1_pair)
    · exact isCap_of_threeAPFree
        (V003.threeAPFree_of_mask 6 codes2 mask2 codes2_lt codes2_mem codes2_pair)
  e1 := by
    intro x hx y hy z hz
    have hx' : x ∈ A0 := hx
    have hy' : y ∈ A0 := hy
    have hz' : z ∈ A1 ∪ A2 := hz
    rw [A0, List.mem_toFinset, List.mem_map] at hx' hy'
    obtain ⟨cx, hcx, rfl⟩ := hx'
    obtain ⟨cy, hcy, rfl⟩ := hy'
    rw [Finset.mem_union, A1, A2, List.mem_toFinset, List.mem_toFinset, List.mem_map,
      List.mem_map] at hz'
    rcases hz' with ⟨cz, hcz, rfl⟩ | ⟨cz, hcz, rfl⟩
    · exact no_sum_of_mask codes0_lt codes1_lt codes0_mem codes1_mem (e1_mask cx hcx).1 cy hcy cz hcz
    · exact no_sum_of_mask codes0_lt codes2_lt codes0_mem codes2_mem (e1_mask cx hcx).2 cy hcy cz hcz
  e2 := by
    intro x hx y hy z hz
    have hx' : x ∈ A0 := hx
    have hy' : y ∈ A1 := hy
    have hz' : z ∈ A2 := hz
    rw [A0, List.mem_toFinset, List.mem_map] at hx'
    rw [A1, List.mem_toFinset, List.mem_map] at hy'
    rw [A2, List.mem_toFinset, List.mem_map] at hz'
    obtain ⟨cx, hcx, rfl⟩ := hx'
    obtain ⟨cy, hcy, rfl⟩ := hy'
    obtain ⟨cz, hcz, rfl⟩ := hz'
    exact no_sum_of_mask codes1_lt codes2_lt codes1_mem codes2_mem (e2_mask cx hcx) cy hcy cz hcz

-- ## The admissible set `I(m, m-1)`: `tri m r` has its single zero at `r`, ones before, twos after.

def tri (m : ℕ) (r : Fin m) : Fin m → Fin 3 :=
  fun j => if j < r then 1 else if j = r then 0 else 2

theorem tri_lt {m : ℕ} {r k : Fin m} (h : k < r) : tri m r k = 1 := by simp [tri, h]

theorem tri_self {m : ℕ} (r : Fin m) : tri m r r = 0 := by simp [tri]

theorem tri_gt {m : ℕ} {r k : Fin m} (h : r < k) : tri m r k = 2 := by
  simp [tri, not_lt.mpr h.le, h.ne']

theorem tri_ne_zero {m : ℕ} {r k : Fin m} (h : k ≠ r) : tri m r k ≠ 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [tri_lt h]; decide
  · rw [tri_gt h]; decide

theorem tri_inj (m : ℕ) : Function.Injective (tri m) := by
  intro r r' h
  by_contra hne
  have := congrFun h r
  rw [tri_self] at this
  exact tri_ne_zero hne this.symm

def Sm (m : ℕ) : Finset (Fin m → Fin 3) := Finset.univ.image (tri m)

theorem Sm_admissible (m : ℕ) : Admissible (Sm m) where
  pair := by
    intro s hs t ht hst
    rw [Sm, Finset.mem_image] at hs ht
    obtain ⟨r, -, rfl⟩ := hs
    obtain ⟨r', -, rfl⟩ := ht
    have hrr : r ≠ r' := fun h => hst (h ▸ rfl)
    exact ⟨r, tri_self r, tri_ne_zero hrr⟩
  triple := by
    intro s hs t ht u hu hst htu hsu
    rw [Sm, Finset.mem_image] at hs ht hu
    obtain ⟨a, -, rfl⟩ := hs
    obtain ⟨b, -, rfl⟩ := ht
    obtain ⟨c, -, rfl⟩ := hu
    have hab : a ≠ b := fun h => hst (h ▸ rfl)
    have hbc : b ≠ c := fun h => htu (h ▸ rfl)
    have hac : a ≠ c := fun h => hsu (h ▸ rfl)
    rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
      rcases lt_or_gt_of_ne hac with h3 | h3
    · exact ⟨b, by rw [tri_gt h1, tri_self, tri_lt h2]; unfold Good; decide⟩
    · exact absurd (h1.trans h2) (lt_asymm h3)
    · exact ⟨c, by rw [tri_gt h3, tri_lt h2, tri_self]; unfold Good; decide⟩
    · exact ⟨a, by rw [tri_self, tri_lt h1, tri_gt h3]; unfold Good; decide⟩
    · exact ⟨a, by rw [tri_self, tri_gt h1, tri_lt h3]; unfold Good; decide⟩
    · exact ⟨c, by rw [tri_lt h3, tri_gt h2, tri_self]; unfold Good; decide⟩
    · exact absurd (h2.trans h1) (lt_asymm h3)
    · exact ⟨b, by rw [tri_lt h1, tri_self, tri_gt h2]; unfold Good; decide⟩

theorem card_ext_Sm (m : ℕ) : (ext A6 (Sm m)).card = fam m := by
  rw [card_ext A6_ext (Sm_admissible m) three_add, Sm,
    Finset.sum_image (fun r _ r' _ h => tri_inj m h)]
  have hprod : ∀ r : Fin m, ∏ j, (A6 (tri m r j)).card = 12 * 112 ^ (m - 1) := by
    intro r
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), tri_self,
      show (A6 0).card = 12 from A0_card]
    congr 1
    rw [Finset.prod_congr rfl (g := fun _ => 112) ?_, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
    intro j hj
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · rw [tri_lt h]; exact A1_card
    · rw [tri_gt h]; exact A2_card
  simp only [hprod, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, fam]

-- The family: a cap of size `fam m = m · 12 · 112 ^ (m - 1)` in `F₃^(6m)`.
theorem fam_le (m : ℕ) (hm : 1 ≤ m) : fam m ≤ SqueezeBench.CapSet.f (m * 6) := by
  have hcap : IsCap ((ext A6 (Sm m)).map ⟨flatHom m 6, flat_injective m 6⟩) :=
    (isCap_ext A6_ext (Sm_admissible m)).map _ _
  have h := card_le_f (by omega) hcap
  rwa [Finset.card_map, card_ext_Sm] at h

-- ## The dynamic programme, as in V004, with the family as extra rows.

theorem foldl_le {α : Type*} {l : List α} {F : ℕ → α → ℕ} {B : ℕ}
    (hF : ∀ acc, acc ≤ B → ∀ a ∈ l, F acc a ≤ B) : ∀ acc, acc ≤ B → l.foldl F acc ≤ B := by
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons a l ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih (fun acc hacc q hq => hF acc hacc q (by simp [hq])) _ (hF acc hacc a (by simp))

theorem dp_length : ∀ k, (dp k).length = k + 1
  | 0 => rfl
  | k + 1 => by simp [dp, dp_length k]

theorem best_succ (k : ℕ) : best (k + 1) = step (dp k) := by
  rw [best, dp, List.headD_cons]

theorem best_zero : best 0 = 1 := rfl

theorem dp_getD : ∀ k j, j ≤ k → (dp k).getD j 0 = best (k - j)
  | 0, 0, _ => rfl
  | 0, j + 1, h => by omega
  | k + 1, 0, _ => by rw [Nat.sub_zero, best_succ, dp, List.getD_cons_zero]
  | k + 1, j + 1, h => by
    rw [dp, List.getD_cons_succ, dp_getD k j (by omega), Nat.add_sub_add_right]

theorem dp_getD_of_gt (k j : ℕ) (h : k < j) : (dp k).getD j 0 = 0 :=
  List.getD_eq_default _ _ (by rw [dp_length]; omega)

-- One product term of the programme is bounded by `f (k + 1)`.
theorem term_le (k : ℕ) (ih : ∀ i < k + 1, 1 ≤ i → best i ≤ SqueezeBench.CapSet.f i)
    {d s : ℕ} (hd : 1 ≤ d) (hs : s ≤ SqueezeBench.CapSet.f d) :
    s * (dp k).getD (d - 1) 0 ≤ SqueezeBench.CapSet.f (k + 1) := by
  by_cases hdk : d ≤ k + 1
  · rw [dp_getD k (d - 1) (by omega)]
    by_cases heq : d = k + 1
    · rw [show k - (d - 1) = 0 by omega, best_zero, mul_one, ← heq]
      exact hs
    · have h1 : 1 ≤ k - (d - 1) := by omega
      have hrec := ih (k - (d - 1)) (by omega) h1
      calc s * best (k - (d - 1))
          ≤ SqueezeBench.CapSet.f d * SqueezeBench.CapSet.f (k - (d - 1)) :=
            Nat.mul_le_mul hs hrec
        _ ≤ SqueezeBench.CapSet.f (d + (k - (d - 1))) := V001.f_mul_le _ _ hd h1
        _ = SqueezeBench.CapSet.f (k + 1) := by rw [show d + (k - (d - 1)) = k + 1 by omega]
  · rw [dp_getD_of_gt k (d - 1) (by omega), mul_zero]
    exact Nat.zero_le _

theorem best_le : ∀ n, 1 ≤ n → best n ≤ SqueezeBench.CapSet.f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [best_succ, step, dp_length]
    have hin : V004.tbl.foldl (fun acc p => max acc (p.2 * (dp k).getD (p.1 - 1) 0)) 0
        ≤ SqueezeBench.CapSet.f (k + 1) :=
      foldl_le (fun acc hacc p hp => max_le hacc (term_le k ih (V004.tbl_pos p hp) (V004.tbl_valid p hp)))
        0 (Nat.zero_le _)
    exact foldl_le (fun acc hacc i _ => max_le hacc
      (term_le k ih (by omega) (by rw [mul_comm]; exact fam_le (i + 1) (by omega)))) _ hin

theorem best_valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f
    (SqueezeBench.pin SqueezeBench.CapSet.nMin best) :=
  SqueezeBench.pin_lowerBoundHolds fun n hn => best_le n (by simpa using hn)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.CapSet.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.CapSet.Lower.V004.valid best_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.CapSet.Lower.V004.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.CapSet.nMin SqueezeBench.CapSet.Lower.V004.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.CapSet.nMin) (n₀ := 60) (by decide)
    (by decide +kernel)

end SqueezeBench.CapSet.Lower.V005
