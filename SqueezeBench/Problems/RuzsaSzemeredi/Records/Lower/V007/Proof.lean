import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V007.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V006.Proof

/-! Record V007 for RuzsaSzemeredi, lower direction, by trial claude-fable: the three obligations.

**Caps.** A cap in `F₃^k` is a 3-AP-free set: in characteristic three `a + c = 2b` reads
`a + b + c = 0`, so the three points of a line sum to zero. Each explicit cap is supplied as a list
of base-3 codes; `CapCode.threeAPFree_of_pairwise` turns one pairwise kernel check ("the third point
of the line through two listed codes is not listed", a bitmask lookup) into `ThreeAPFree` of the
decoded set. The caps are the elliptic-quadric cone (`20` in `F₃^4`), the Hill cap in its
Calderbank–Kantor form (`112` in `F₃^6`) and its affine part off a tangent hyperplane (`45` in
`F₃^5`), the graph of `x² + y²` (`9` in `F₃^3`), and products with `{1, 2}`.

**Two graphs.** `CayleyCap` shows that the Cayley graph of a symmetric cap `C = -C ∌ 0` in a group
of exponent three is locally linear with at least `|G| · |C| / 6` triangles. `trip` is Mathlib's
tripartite construction `addRothNumber_le_ruzsaSzemerediNumber` over the ring
`Z_{2m+1} × F₃^(6q) × F₃^r`, fed with the product of V006's integer 3-AP-free set and the caps. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V007

open SqueezeBench Finset SimpleGraph

/-! ### Base-3 codes for vectors of `F₃^k` -/

namespace CapCode

/-- Digit-wise sum mod 3 of two base-3 codes, on `k` digits. -/
def add3 : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => (a % 3 + b % 3) % 3 + 3 * add3 k (a / 3) (b / 3)

/-- Digit-wise negation mod 3 of a base-3 code, on `k` digits. -/
def neg3 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => (3 - a % 3) % 3 + 3 * neg3 k (a / 3)

/-- Decode a base-3 code into a vector of `F₃^k`: digit `i` is coordinate `i`. -/
def dec (k : ℕ) (e : ℕ) : Fin k → ZMod 3 := fun i => ((e / 3 ^ (i : ℕ)) % 3 : ℕ)

theorem dec_zero (k e : ℕ) : dec (k + 1) e 0 = ((e % 3 : ℕ) : ZMod 3) := by simp [dec]

theorem dec_succ (k e : ℕ) (i : Fin k) : dec (k + 1) e i.succ = dec k (e / 3) i := by
  simp only [dec, Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

theorem dec_add (k : ℕ) : ∀ a b, dec k (add3 k a b) = dec k a + dec k b := by
  induction k with
  | zero => intro a b; funext i; exact i.elim0
  | succ k ih =>
    intro a b
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, dec_zero, add3, Nat.add_mul_mod_self_left, Nat.mod_mod,
        ZMod.natCast_mod, Nat.cast_add]
    · simp only [Pi.add_apply, dec_succ, add3]
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)),
        zero_add]
      exact congr_fun (ih (a / 3) (b / 3)) j

theorem neg_digit (x : ℕ) (hx : x < 3) : (((3 - x) % 3 : ℕ) : ZMod 3) = -(x : ZMod 3) := by
  interval_cases x <;> decide

theorem dec_neg (k : ℕ) : ∀ a, dec k (neg3 k a) = -dec k a := by
  induction k with
  | zero => intro a; funext i; exact i.elim0
  | succ k ih =>
    intro a
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.neg_apply, dec_zero, neg3, Nat.add_mul_mod_self_left, Nat.mod_mod]
      exact neg_digit _ (Nat.mod_lt _ (by norm_num))
    · simp only [Pi.neg_apply, dec_succ, neg3]
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)),
        zero_add]
      exact congr_fun (ih (a / 3)) j

theorem add3_lt (k : ℕ) : ∀ a b, add3 k a b < 3 ^ k := by
  induction k with
  | zero => intro a b; simp [add3]
  | succ k ih =>
    intro a b
    simp only [add3, pow_succ]
    have := ih (a / 3) (b / 3)
    have h : (a % 3 + b % 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega

theorem neg3_lt (k : ℕ) : ∀ a, neg3 k a < 3 ^ k := by
  induction k with
  | zero => intro a; simp [neg3]
  | succ k ih =>
    intro a
    simp only [neg3, pow_succ]
    have := ih (a / 3)
    have h : (3 - a % 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega

theorem add3_comm (k : ℕ) : ∀ a b, add3 k a b = add3 k b a := by
  induction k with
  | zero => intro a b; simp [add3]
  | succ k ih => intro a b; simp only [add3, Nat.add_comm (a % 3), ih (a / 3)]

theorem dec_inj (k : ℕ) : ∀ a b, a < 3 ^ k → b < 3 ^ k → dec k a = dec k b → a = b := by
  induction k with
  | zero => intro a b ha hb _; simp at ha hb; omega
  | succ k ih =>
    intro a b ha hb h
    have h0 := congr_fun h 0
    rw [dec_zero, dec_zero] at h0
    have h0' : a % 3 = b % 3 := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h0
      simpa [Nat.mod_mod] using this
    have h1 : dec k (a / 3) = dec k (b / 3) := by
      funext j; rw [← dec_succ, ← dec_succ, h]
    have ha' : a / 3 < 3 ^ k := by rw [pow_succ] at ha; omega
    have hb' : b / 3 < 3 ^ k := by rw [pow_succ] at hb; omega
    have := ih _ _ ha' hb' h1
    omega

theorem dec_zero_eq (k : ℕ) : dec k 0 = 0 := by
  funext i; simp [dec]

/-- A bitmask with bit `x` set for each `x ∈ L`. -/
def mask (L : List ℕ) : ℕ := L.foldl (fun acc x => acc ||| 2 ^ x) 0

theorem testBit_foldl (L : List ℕ) : ∀ (acc e : ℕ),
    (L.foldl (fun acc x => acc ||| 2 ^ x) acc).testBit e = (acc.testBit e || decide (e ∈ L)) := by
  induction L with
  | nil => intro acc e; simp
  | cons x L ih =>
    intro acc e
    simp only [List.foldl_cons, ih, Nat.testBit_lor, Nat.testBit_two_pow, List.mem_cons]
    rcases eq_or_ne x e with rfl | h
    · simp
    · by_cases h' : e ∈ L <;> simp [h, h.symm, h']

theorem testBit_mask (L : List ℕ) (e : ℕ) : (mask L).testBit e = true ↔ e ∈ L := by
  simp [mask, testBit_foldl]

/-- The set of vectors encoded by a list of codes. -/
def vecs (k : ℕ) (L : List ℕ) : Finset (Fin k → ZMod 3) := (L.map (dec k)).toFinset

theorem mem_vecs {k : ℕ} {L : List ℕ} {x : Fin k → ZMod 3} :
    x ∈ vecs k L ↔ ∃ a ∈ L, dec k a = x := by
  simp [vecs]

/-- The pairwise check: the third point of the line through two listed codes is not listed. -/
def PairOk (M k a b : ℕ) : Prop := M.testBit (neg3 k (add3 k a b)) = false

instance (M k : ℕ) : DecidableRel (PairOk M k) :=
  fun a b => inferInstanceAs (Decidable (M.testBit (neg3 k (add3 k a b)) = false))

theorem two_eq_neg (v : Fin k → ZMod 3) : v + v = -v := by
  funext i; simp only [Pi.add_apply, Pi.neg_apply]
  generalize v i = t; revert t; decide

theorem threeAPFree_of_pairwise (k : ℕ) (L : List ℕ) (hlt : ∀ a ∈ L, a < 3 ^ k)
    (hchk : L.Pairwise (PairOk (mask L) k)) :
    ThreeAPFree (vecs k L : Set (Fin k → ZMod 3)) := by
  haveI hsymm : Std.Symm (PairOk (mask L) k) :=
    ⟨fun a b h => by unfold PairOk at *; rwa [add3_comm]⟩
  have hall := List.Pairwise.forall hchk
  intro x hx y hy z hz hxz
  rw [Finset.mem_coe, mem_vecs] at hx hy hz
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hz
  by_cases hac : a = c
  · subst hac
    rw [two_eq_neg, two_eq_neg, neg_inj] at hxz
    exact hxz
  · exfalso
    have hok := hall ha hc hac
    unfold PairOk at hok
    have hb' : dec k b = dec k (neg3 k (add3 k a c)) := by
      rw [dec_neg, dec_add, hxz, two_eq_neg, neg_neg]
    have := dec_inj k _ _ (hlt b hb) (neg3_lt k _) hb'
    rw [← this] at hok
    have hmem := (testBit_mask L b).2 hb
    rw [hmem] at hok
    exact Bool.noConfusion hok

theorem card_vecs (k : ℕ) (L : List ℕ) (hlt : ∀ a ∈ L, a < 3 ^ k) (hnd : L.Nodup) :
    (vecs k L).card = L.length := by
  unfold vecs
  rw [List.toFinset_card_of_nodup, List.length_map]
  exact hnd.map_on (fun a ha b hb h => dec_inj k a b (hlt a ha) (hlt b hb) h)

theorem neg_mem_vecs (k : ℕ) (L : List ℕ)
    (hneg : ∀ a ∈ L, (mask L).testBit (neg3 k a) = true) :
    ∀ x ∈ vecs k L, -x ∈ vecs k L := by
  intro x hx
  rw [mem_vecs] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨neg3 k a, (testBit_mask _ _).1 (hneg a ha), dec_neg k a⟩

theorem zero_notMem_vecs (k : ℕ) (L : List ℕ) (hlt : ∀ a ∈ L, a < 3 ^ k)
    (h0 : (mask L).testBit 0 = false) : (0 : Fin k → ZMod 3) ∉ vecs k L := by
  intro hx
  rw [mem_vecs] at hx
  obtain ⟨a, ha, hda⟩ := hx
  have := dec_inj k a 0 (hlt a ha) (by positivity) (hda.trans (dec_zero_eq k).symm)
  subst this
  have hmem := (testBit_mask L 0).2 ha
  rw [hmem] at h0
  exact Bool.noConfusion h0

end CapCode

open CapCode

/-! ### The explicit caps, as lists of base-3 codes (digit `i` is coordinate `i`) -/

/-- The 9-cap `{(x, y, x² + y²)}` in `F₃^3`. -/
def L9 : List ℕ := [0, 10, 11, 12, 15, 22, 23, 25, 26]

/-- The 20-cap in `F₃^4`: the nonzero solutions of `x₀² + x₁² + x₂² + 2x₃² = 0`, the cone over an
elliptic quadric of `PG(3,3)`. Symmetric. -/
def L20 : List ℕ := [13, 14, 16, 17, 22, 23, 25, 26, 28, 29, 30, 33, 36, 45, 55, 56, 57, 60, 63, 72]

/-- The 45-cap in `F₃^5`: the points `x` of the Hill cap `L112` with `x₀ + x₁ + x₂ = 1`, in the
coordinates `x₁, …, x₅` (`x₀` is determined). -/
def L45 : List ℕ := [4, 5, 7, 15, 24, 35, 36, 37, 45, 46, 62, 63, 64, 72, 73, 83, 91, 93, 100, 102, 108, 111, 130, 131, 133, 135, 138, 148, 149, 151, 164, 172, 174, 181, 183, 189, 192, 202, 203, 205, 216, 219, 238, 239, 241]

/-- The Hill cap, `112` points of `F₃^6` (Calderbank–Kantor form): with coordinates indexed by
`∞, 0, 1, 2, 3, 4` (here digits `0, …, 5`), the vectors supported on one of the ten triples
`∞01, ∞12, ∞23, ∞34, ∞40, 013, 124, 023, 134, 024` with nonzero entries there, and the vectors
with all entries nonzero and product `1`. Symmetric, and contained in `∑ xᵢ² = 0`. -/
def L112 : List ℕ := [13, 14, 16, 17, 22, 23, 25, 26, 37, 38, 46, 47, 64, 65, 73, 74, 93, 96, 102, 105, 109, 110, 111, 114, 136, 137, 138, 141, 174, 177, 183, 186, 190, 191, 192, 195, 217, 218, 219, 222, 247, 248, 250, 251, 273, 276, 279, 288, 300, 303, 306, 315, 325, 326, 333, 342, 364, 368, 374, 376, 392, 394, 400, 404, 406, 407, 414, 423, 446, 448, 454, 458, 472, 476, 482, 484, 490, 491, 493, 494, 516, 519, 522, 531, 543, 546, 549, 558, 568, 569, 576, 585, 608, 610, 616, 620, 634, 638, 644, 646, 649, 650, 657, 666, 688, 692, 698, 700, 716, 718, 724, 728]

/-- The symmetric 8-cap `{1, 2}^3`. -/
def S8 : List ℕ := [13, 14, 16, 17, 22, 23, 25, 26]

/-- The symmetric 40-cap `{1, 2} × L20` in `F₃^5`. -/
def S40 : List ℕ := [40, 41, 43, 44, 49, 50, 52, 53, 67, 68, 70, 71, 76, 77, 79, 80, 85, 86, 88, 89, 91, 92, 100, 101, 109, 110, 136, 137, 166, 167, 169, 170, 172, 173, 181, 182, 190, 191, 217, 218]

/-- The cap used in `F₃^r` for the tripartite construction, `r ≤ 5`; it has `capr r` points. -/
def capL (r : ℕ) : List ℕ :=
  if r = 0 then [0] else if r = 1 then [0, 1] else if r = 2 then [0, 1, 3, 4]
  else if r = 3 then L9 else if r = 4 then L20 else L45

/-- The symmetric cap used in `F₃^r` for the Cayley construction, `r ≤ 5`; it has `symr r`
points, and does not contain `0` when `r ≥ 1`. -/
def symL (r : ℕ) : List ℕ :=
  if r = 0 then [0] else if r = 1 then [1, 2] else if r = 2 then [4, 5, 7, 8]
  else if r = 3 then S8 else if r = 4 then L20 else S40

/-! The kernel checks the supplied data: codes in range, no repeated code, the pairwise line
check, and (for the symmetric caps) closure under negation and absence of `0`. -/

theorem L112_lt : ∀ a ∈ L112, a < 3 ^ 6 := by decide +kernel
theorem L112_pw : L112.Pairwise (PairOk (mask L112) 6) := by decide +kernel
theorem L112_nodup : L112.Nodup := by decide +kernel
theorem L112_neg : ∀ a ∈ L112, (mask L112).testBit (neg3 6 a) = true := by decide +kernel
theorem L112_zero : (mask L112).testBit 0 = false := by decide +kernel

theorem capL_lt (r : ℕ) (hr : r ≤ 5) : ∀ a ∈ capL r, a < 3 ^ r := by
  interval_cases r <;> decide +kernel
theorem capL_pw (r : ℕ) (hr : r ≤ 5) : (capL r).Pairwise (PairOk (mask (capL r)) r) := by
  interval_cases r <;> decide +kernel
theorem capL_nodup (r : ℕ) (hr : r ≤ 5) : (capL r).Nodup := by
  interval_cases r <;> decide +kernel
theorem capL_length (r : ℕ) (hr : r ≤ 5) : (capL r).length = capr r := by
  interval_cases r <;> rfl

theorem symL_lt (r : ℕ) (hr : r ≤ 5) : ∀ a ∈ symL r, a < 3 ^ r := by
  interval_cases r <;> decide +kernel
theorem symL_pw (r : ℕ) (hr : r ≤ 5) : (symL r).Pairwise (PairOk (mask (symL r)) r) := by
  interval_cases r <;> decide +kernel
theorem symL_nodup (r : ℕ) (hr : r ≤ 5) : (symL r).Nodup := by
  interval_cases r <;> decide +kernel
theorem symL_length (r : ℕ) (hr : r ≤ 5) : (symL r).length = symr r := by
  interval_cases r <;> rfl
theorem symL_neg (r : ℕ) (hr : r ≤ 5) :
    ∀ a ∈ symL r, (mask (symL r)).testBit (neg3 r a) = true := by
  interval_cases r <;> decide +kernel
theorem symL_zero (r : ℕ) (hr : r ≤ 5) (hr1 : 1 ≤ r) : (mask (symL r)).testBit 0 = false := by
  interval_cases r <;> decide +kernel

/-! ### The caps as finsets -/

/-- The Hill cap as a subset of `F₃^6`. -/
def C112 : Finset (Fin 6 → ZMod 3) := vecs 6 L112

theorem C112_free : ThreeAPFree (C112 : Set (Fin 6 → ZMod 3)) :=
  threeAPFree_of_pairwise 6 L112 L112_lt L112_pw
theorem C112_card : C112.card = 112 := card_vecs 6 L112 L112_lt L112_nodup
theorem C112_neg : ∀ x ∈ C112, -x ∈ C112 := neg_mem_vecs 6 L112 L112_neg
theorem C112_zero : (0 : Fin 6 → ZMod 3) ∉ C112 := zero_notMem_vecs 6 L112 L112_lt L112_zero
theorem C112_le : 112 ≤ addRothNumber (univ : Finset (Fin 6 → ZMod 3)) :=
  C112_card ▸ ThreeAPFree.le_addRothNumber C112_free (subset_univ _)

theorem capr_le (r : ℕ) (hr : r ≤ 5) : capr r ≤ addRothNumber (univ : Finset (Fin r → ZMod 3)) := by
  calc capr r = (vecs r (capL r)).card := by
        rw [card_vecs r _ (capL_lt r hr) (capL_nodup r hr), capL_length r hr]
    _ ≤ _ := ThreeAPFree.le_addRothNumber
        (threeAPFree_of_pairwise r _ (capL_lt r hr) (capL_pw r hr)) (subset_univ _)

/-- The symmetric cap in `F₃^r`. -/
def symcap (r : ℕ) : Finset (Fin r → ZMod 3) := vecs r (symL r)

theorem symcap_free (r : ℕ) (hr : r ≤ 5) : ThreeAPFree (symcap r : Set (Fin r → ZMod 3)) :=
  threeAPFree_of_pairwise r _ (symL_lt r hr) (symL_pw r hr)
theorem symcap_card (r : ℕ) (hr : r ≤ 5) : (symcap r).card = symr r := by
  rw [symcap, card_vecs r _ (symL_lt r hr) (symL_nodup r hr), symL_length r hr]
theorem symcap_neg (r : ℕ) (hr : r ≤ 5) : ∀ x ∈ symcap r, -x ∈ symcap r :=
  neg_mem_vecs r _ (symL_neg r hr)
theorem symcap_zero (r : ℕ) (hr : r ≤ 5) (hr1 : 1 ≤ r) : (0 : Fin r → ZMod 3) ∉ symcap r :=
  zero_notMem_vecs r _ (symL_lt r hr) (symL_zero r hr hr1)

/-! ### Cayley graphs of symmetric caps -/

namespace CayleyCap

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The Cayley graph of a symmetric set `S`: `x ~ y` iff `y - x ∈ S`. -/
def cay (S : Finset G) (hS : ∀ a ∈ S, -a ∈ S) : SimpleGraph G where
  Adj x y := x ≠ y ∧ y - x ∈ S
  symm := ⟨fun x y ⟨hne, h⟩ => ⟨hne.symm, by have := hS _ h; rwa [neg_sub] at this⟩⟩
  loopless := ⟨fun x ⟨h, _⟩ => h rfl⟩

instance (S : Finset G) (hS : ∀ a ∈ S, -a ∈ S) : DecidableRel (cay S hS).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ y - x ∈ S))

omit [Fintype G] [DecidableEq G] in
/-- `x + x = -x` in a group of exponent three. -/
theorem two_eq_neg (h3 : ∀ x : G, x + x + x = 0) (x : G) : x + x = -x :=
  eq_neg_of_add_eq_zero_left (h3 x)

omit [Fintype G] [DecidableEq G] in
/-- The third vertex of a triangle through an edge is forced: `z = -(x + y)`. -/
theorem third_eq (S : Finset G) (hS : ∀ a ∈ S, -a ∈ S) (h3 : ∀ x : G, x + x + x = 0)
    (hAP : ThreeAPFree (S : Set G)) {x y z : G} (hxy : (cay S hS).Adj x y)
    (hxz : (cay S hS).Adj x z) (hyz : (cay S hS).Adj y z) : z = -(x + y) := by
  obtain ⟨_, ha⟩ := hxy
  obtain ⟨_, hb⟩ := hxz
  obtain ⟨_, hc⟩ := hyz
  have hnb := hS _ hb
  have key : (y - x) + (z - y) = -(z - x) + -(z - x) := by
    rw [two_eq_neg h3, neg_neg]; abel
  have h := hAP ha hnb hc key
  rw [neg_sub, sub_eq_sub_iff_add_eq_add] at h
  have e : z = (x + x) - y := eq_sub_of_add_eq' h
  rw [e, two_eq_neg h3 x]; abel

omit [Fintype G] in
/-- A triangle through the edge `xy` is `{x, y, -(x+y)}`. -/
theorem triangle_eq (S : Finset G) (hS : ∀ a ∈ S, -a ∈ S) (h3 : ∀ x : G, x + x + x = 0)
    (hAP : ThreeAPFree (S : Set G)) {x y : G} (hxy : x ≠ y) {u : Finset G}
    (hu : (cay S hS).IsNClique 3 u) (hxu : x ∈ u) (hyu : y ∈ u) : u = {x, y, -(x + y)} := by
  have hadj : (cay S hS).Adj x y := hu.isClique hxu hyu hxy
  refine eq_of_subset_of_card_le ?_ ?_
  · intro z hz
    simp only [mem_insert, mem_singleton]
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr (Or.inl hzy)
    exact Or.inr (Or.inr (third_eq S hS h3 hAP hadj (hu.isClique hxu hz (Ne.symm hzx))
      (hu.isClique hyu hz (Ne.symm hzy))))
  · rw [hu.card_eq]; exact card_le_three

theorem locallyLinear (S : Finset G) (hS : ∀ a ∈ S, -a ∈ S) (h3 : ∀ x : G, x + x + x = 0)
    (hAP : ThreeAPFree (S : Set G)) (h0 : (0 : G) ∉ S) : (cay S hS).LocallyLinear := by
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    rw [mem_cliqueSet_iff] at hs ht
    by_contra hcon
    rw [Set.not_subsingleton_iff] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := hcon
    simp only [Set.mem_inter_iff, mem_coe] at hx hy
    exact hst ((triangle_eq S hS h3 hAP hxy hs hx.1 hy.1).trans
      (triangle_eq S hS h3 hAP hxy ht hx.2 hy.2).symm)
  · intro x y hxy
    obtain ⟨hne, ha⟩ := hxy
    refine ⟨{x, y, -(x + y)}, ?_, by simp, by simp⟩
    have hna : -(y - x) ∈ S := hS _ ha
    have h2 : -(x + y) - x ∈ S := by
      have : -(x + y) - x = -(y - x) - (x + x + x) := by abel
      rw [this, h3 x, sub_zero]; exact hna
    have h2' : -(x + y) - y ∈ S := by
      have : -(x + y) - y = (y - x) - (y + y + y) := by abel
      rw [this, h3 y, sub_zero]; exact ha
    have hxz : x ≠ -(x + y) := by
      intro h; apply h0
      have : -(x + y) - x = 0 := by rw [← h]; simp
      rw [← this]; exact h2
    have hyz : y ≠ -(x + y) := by
      intro h; apply h0
      have : -(x + y) - y = 0 := by rw [← h]; simp
      rw [← this]; exact h2'
    rw [is3Clique_iff]
    exact ⟨x, y, -(x + y), ⟨hne, ha⟩, ⟨hxz, h2⟩, ⟨hyz, h2'⟩, rfl⟩

/-- Six times the number of triangles is at least `|G| · |S|`: `(x, a) ↦ {x, x+a, x+2a}` maps
`G × S` onto triangles, at most six to one. -/
theorem card_mul_le (S : Finset G) (hS : ∀ a ∈ S, -a ∈ S) (h3 : ∀ x : G, x + x + x = 0)
    (h0 : (0 : G) ∉ S) :
    Fintype.card G * S.card ≤ 6 * ((cay S hS).cliqueFinset 3).card := by
  let φ : G × G → Finset G := fun p => {p.1, p.1 + p.2, p.1 + p.2 + p.2}
  have hmaps : ∀ p ∈ (univ : Finset G) ×ˢ S, φ p ∈ (cay S hS).cliqueFinset 3 := by
    rintro ⟨x, a⟩ hp
    simp only [mem_product, mem_univ, true_and] at hp
    rw [mem_cliqueFinset_iff, is3Clique_iff]
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ hp)
    have h2a : a + a ∈ S := by rw [two_eq_neg h3]; exact hS _ hp
    have h2a0 : a + a ≠ 0 := by
      rw [two_eq_neg h3]; exact fun h => ha0 (neg_eq_zero.1 h)
    refine ⟨x, x + a, x + a + a, ⟨?_, by simpa⟩, ⟨?_, by simpa [add_assoc]⟩, ⟨?_, by simpa⟩,
      rfl⟩
    · intro h; exact ha0 (by simpa using h.symm)
    · intro h; exact h2a0 (by rw [add_assoc] at h; simpa using h.symm)
    · intro h; exact ha0 (by simpa using h.symm)
  have hfib : ∀ t ∈ (cay S hS).cliqueFinset 3,
      ((univ ×ˢ S).filter (fun p => φ p = t)).card ≤ 6 := by
    intro t ht
    have hcard : t.card = 3 := (mem_cliqueFinset_iff.1 ht).card_eq
    have : ((univ ×ˢ S).filter (fun p => φ p = t)).card ≤ t.offDiag.card := by
      refine card_le_card_of_injOn (fun p => (p.1, p.1 + p.2)) ?_ ?_
      · rintro ⟨x, a⟩ hp
        simp only [coe_filter, mem_product, mem_univ, true_and, Set.mem_setOf_eq] at hp
        obtain ⟨ha, hφ⟩ := hp
        have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
        rw [mem_coe, mem_offDiag]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hφ]; simp [φ]
        · rw [← hφ]; simp [φ]
        · simp only; intro h; exact ha0 (by simpa using h.symm)
      · rintro ⟨x, a⟩ _ ⟨y, b⟩ _ h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        simp only [add_right_inj] at h2
        rw [h2]
    rw [offDiag_card, hcard] at this
    exact this
  calc Fintype.card G * S.card = ((univ : Finset G) ×ˢ S).card := by simp
    _ ≤ 6 * ((cay S hS).cliqueFinset 3).card :=
        card_le_mul_card_image_of_maps_to hmaps 6 hfib

end CayleyCap

/-! ### The Cayley construction on `F₃^(6q) × F₃^r` -/

theorem three_zero_zmod (x : ZMod 3) : x + x + x = 0 := by revert x; decide

/-- The group of the Cayley construction. -/
abbrev CG (q r : ℕ) : Type := (Fin q → Fin 6 → ZMod 3) × (Fin r → ZMod 3)

theorem cg_three (q r : ℕ) (x : CG q r) : x + x + x = 0 :=
  Prod.ext (funext fun _ => funext fun _ => three_zero_zmod _) (funext fun _ => three_zero_zmod _)

/-- The symmetric cap `C112^q × symcap r` of the Cayley construction. -/
def CS (q r : ℕ) : Finset (CG q r) := (Fintype.piFinset fun _ : Fin q => C112) ×ˢ symcap r

theorem CS_neg (q r : ℕ) (hr : r ≤ 5) : ∀ a ∈ CS q r, -a ∈ CS q r := by
  rintro ⟨x, y⟩ h
  rw [CS, mem_product] at h ⊢
  refine ⟨?_, symcap_neg r hr y h.2⟩
  rw [Fintype.mem_piFinset] at h ⊢
  intro i
  exact C112_neg _ (h.1 i)

theorem CS_free (q r : ℕ) (hr : r ≤ 5) : ThreeAPFree (CS q r : Set (CG q r)) := by
  rw [CS, coe_product, Fintype.coe_piFinset]
  exact ThreeAPFree.prod (threeAPFree_pi fun _ => C112_free) (symcap_free r hr)

theorem CS_zero (q r : ℕ) (hr : r ≤ 5) (hqr : 1 ≤ q ∨ 1 ≤ r) : (0 : CG q r) ∉ CS q r := by
  intro h
  rw [CS, mem_product, Fintype.mem_piFinset] at h
  rcases hqr with hq | hr1
  · exact C112_zero (h.1 ⟨0, hq⟩)
  · exact symcap_zero r hr hr1 h.2

theorem CS_card (q r : ℕ) (hr : r ≤ 5) : (CS q r).card = 112 ^ q * symr r := by
  rw [CS, card_product, Fintype.card_piFinset_const, C112_card, symcap_card r hr]

theorem CG_card (q r : ℕ) : Fintype.card (CG q r) = 3 ^ (6 * q) * 3 ^ r := by
  simp [Fintype.card_prod, Fintype.card_pi, ZMod.card, pow_mul]

theorem cay_key (q r : ℕ) (hr : r ≤ 5) (hqr : 1 ≤ q ∨ 1 ≤ r) :
    3 ^ (6 * q) * 3 ^ r * (112 ^ q * symr r) ≤
      6 * SqueezeBench.RuzsaSzemeredi.f (3 ^ (6 * q) * 3 ^ r) := by
  have hS := CS_neg q r hr
  have hLL := CayleyCap.locallyLinear (CS q r) hS (cg_three q r) (CS_free q r hr)
    (CS_zero q r hr hqr)
  have hcnt := CayleyCap.card_mul_le (CS q r) hS (cg_three q r) (CS_zero q r hr hqr)
  rw [CG_card, CS_card q r hr] at hcnt
  have hrs := hLL.le_ruzsaSzemerediNumber
  rw [← ruzsaSzemerediNumberNat_card, CG_card] at hrs
  have h3 : 3 ≤ 3 ^ (6 * q) * 3 ^ r := by
    rcases hqr with hq | hr1
    · calc 3 ≤ 3 ^ (6 * q) := by
            calc 3 = 3 ^ 1 := by norm_num
              _ ≤ 3 ^ (6 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 3 ^ (6 * q) * 3 ^ r := Nat.le_mul_of_pos_right _ (by positivity)
    · calc 3 ≤ 3 ^ r := by
            calc 3 = 3 ^ 1 := by norm_num
              _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
        _ ≤ 3 ^ (6 * q) * 3 ^ r := Nat.le_mul_of_pos_left _ (by positivity)
  rw [SqueezeBench.RuzsaSzemeredi.f_of_le (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]; exact h3)]
  exact hcnt.trans (Nat.mul_le_mul_left _ hrs)

/-! ### The tripartite construction on `Z_{2m+1} × F₃^(6q) × F₃^r` -/

theorem addRothNumber_univ_pow_le {H : Type*} [AddCommMonoid H] [Fintype H] [DecidableEq H]
    (q : ℕ) : addRothNumber (univ : Finset H) ^ q ≤ addRothNumber (univ : Finset (Fin q → H)) := by
  obtain ⟨s, -, hcard, hs⟩ := addRothNumber_spec (univ : Finset H)
  have h := threeAPFree_pi (ι := Fin q) (s := fun _ => (s : Set H)) (fun _ => hs)
  rw [← Fintype.coe_piFinset] at h
  have := ThreeAPFree.le_addRothNumber h (subset_univ _)
  rwa [Fintype.card_piFinset_const, hcard] at this

theorem addRothNumber_univ_prod_le {A B : Type*} [AddCommMonoid A] [Fintype A] [DecidableEq A]
    [AddCommMonoid B] [Fintype B] [DecidableEq B] :
    addRothNumber (univ : Finset A) * addRothNumber (univ : Finset B) ≤
      addRothNumber (univ : Finset (A × B)) := by
  rw [← univ_product_univ]
  exact le_addRothNumber_product _ _

/-- Mathlib's tripartite construction, restated with `ruzsaSzemerediNumberNat`. -/
theorem rs_of_ring (α : Type) [Fintype α] [DecidableEq α] [CommRing α] [Fact (IsUnit (2 : α))] :
    Fintype.card α * addRothNumber (univ : Finset α) ≤
      ruzsaSzemerediNumberNat (3 * Fintype.card α) := by
  have key := addRothNumber_le_ruzsaSzemerediNumber α
  rw [← ruzsaSzemerediNumberNat_card, Fintype.card_sum, Fintype.card_sum] at key
  convert key using 2; ring

/-- The ring of the tripartite construction. -/
abbrev TG (m q r : ℕ) : Type := Fin (2 * m + 1) × (Fin q → Fin 6 → ZMod 3) × (Fin r → ZMod 3)

open scoped Fin.CommRing in
/-- Mathlib's tripartite construction over `TG m q r`, with the product 3-AP-free set. -/
theorem trip (m q r : ℕ) :
    ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r) *
      (rothNumberNat m * addRothNumber (univ : Finset (Fin 6 → ZMod 3)) ^ q *
        addRothNumber (univ : Finset (Fin r → ZMod 3))) ≤
      ruzsaSzemerediNumberNat (3 * ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r)) := by
  have hcop : Nat.Coprime 2 (2 * m + 1) := by simp
  have hu1 : IsUnit (2 : Fin (2 * m + 1)) := by
    simpa using! (ZMod.unitOfCoprime 2 hcop).isUnit
  have hu3 : IsUnit (2 : ZMod 3) := ⟨⟨2, 2, by decide, by decide⟩, rfl⟩
  haveI : Fact (IsUnit (2 : TG m q r)) := ⟨by
    rw [Prod.isUnit_iff, Prod.isUnit_iff]
    refine ⟨hu1, ?_, ?_⟩
    · rw [Pi.isUnit_iff]; intro i; rw [Pi.isUnit_iff]; intro j; exact hu3
    · rw [Pi.isUnit_iff]; intro i; exact hu3⟩
  have hcard : Fintype.card (TG m q r) = (2 * m + 1) * 3 ^ (6 * q) * 3 ^ r := by
    simp [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card, pow_mul]; ring
  have h1 : rothNumberNat m ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) := by
    rw [← Fin.addRothNumber_eq_rothNumberNat (n := 2 * m) (k := m) le_rfl]
    exact addRothNumber.mono (subset_univ _)
  have h2 := addRothNumber_univ_pow_le (H := Fin 6 → ZMod 3) q
  have h3 : rothNumberNat m * addRothNumber (univ : Finset (Fin 6 → ZMod 3)) ^ q *
      addRothNumber (univ : Finset (Fin r → ZMod 3)) ≤
        addRothNumber (univ : Finset (TG m q r)) := by
    calc _ ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) *
          addRothNumber (univ : Finset (Fin q → Fin 6 → ZMod 3)) *
          addRothNumber (univ : Finset (Fin r → ZMod 3)) := by gcongr
      _ ≤ addRothNumber (univ : Finset (Fin (2 * m + 1))) *
          addRothNumber (univ : Finset ((Fin q → Fin 6 → ZMod 3) × (Fin r → ZMod 3))) := by
          rw [mul_assoc]; gcongr; exact addRothNumber_univ_prod_le
      _ ≤ addRothNumber (univ : Finset (TG m q r)) := addRothNumber_univ_prod_le
  have key := rs_of_ring (TG m q r)
  rw [hcard] at key
  exact (Nat.mul_le_mul_left _ h3).trans key

/-- The tripartite bound with the cap sizes of the record. -/
theorem trip_key (m k : ℕ) :
    3 ^ k * (2 * m + 1) * (capB k * rothNumberNat m) ≤
      SqueezeBench.RuzsaSzemeredi.f (3 * (3 ^ k * (2 * m + 1))) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r ≤ 5 ∧ k = 6 * q + r :=
    ⟨k / 6, k % 6, by omega, by omega⟩
  have hcap : capB (6 * q + r) = 112 ^ q * capr r := by
    unfold capB
    have e1 : (6 * q + r) / 6 = q := by omega
    have e2 : (6 * q + r) % 6 = r := by omega
    rw [e1, e2]
  have h := trip m q r
  have h112 := C112_le
  have hr' := capr_le r hr
  have hpos : SqueezeBench.RuzsaSzemeredi.nMin ≤ 3 * (3 ^ (6 * q + r) * (2 * m + 1)) := by
    rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]
    exact Nat.le_mul_of_pos_right 3 (Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega))
  rw [SqueezeBench.RuzsaSzemeredi.f_of_le hpos]
  calc 3 ^ (6 * q + r) * (2 * m + 1) * (capB (6 * q + r) * rothNumberNat m)
      = ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r) * (rothNumberNat m * 112 ^ q * capr r) := by
        rw [hcap, pow_add]; ring
    _ ≤ ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r) *
        (rothNumberNat m * addRothNumber (univ : Finset (Fin 6 → ZMod 3)) ^ q *
          addRothNumber (univ : Finset (Fin r → ZMod 3))) := by gcongr
    _ ≤ ruzsaSzemerediNumberNat (3 * ((2 * m + 1) * 3 ^ (6 * q) * 3 ^ r)) := h
    _ = _ := by congr 1; rw [pow_add]; ring

/-! ### Validity of the record -/

theorem tripAt_le (n k : ℕ) : tripAt n k ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  unfold tripAt
  simp only
  split_ifs with hq
  · exact Nat.zero_le _
  · have hq1 : 1 ≤ n / (3 * 3 ^ k) := Nat.one_le_iff_ne_zero.2 hq
    have hle : 3 * (3 ^ k * (2 * ((n / (3 * 3 ^ k) - 1) / 2) + 1)) ≤ n := by
      have h2 : 2 * ((n / (3 * 3 ^ k) - 1) / 2) + 1 ≤ n / (3 * 3 ^ k) := by omega
      calc 3 * (3 ^ k * (2 * ((n / (3 * 3 ^ k) - 1) / 2) + 1))
          ≤ 3 * (3 ^ k * (n / (3 * 3 ^ k))) := by gcongr
        _ = (3 * 3 ^ k) * (n / (3 * 3 ^ k)) := by ring
        _ ≤ n := Nat.mul_div_le n _
    calc 3 ^ k * (2 * ((n / (3 * 3 ^ k) - 1) / 2) + 1) *
          (capB k * V006.sz ((n / (3 * 3 ^ k) - 1) / 2))
        ≤ 3 ^ k * (2 * ((n / (3 * 3 ^ k) - 1) / 2) + 1) *
          (capB k * rothNumberNat ((n / (3 * 3 ^ k) - 1) / 2)) := by
          gcongr; exact V006.sz_le _
      _ ≤ SqueezeBench.RuzsaSzemeredi.f (3 * (3 ^ k * (2 * ((n / (3 * 3 ^ k) - 1) / 2) + 1))) :=
          trip_key _ _
      _ ≤ SqueezeBench.RuzsaSzemeredi.f n :=
          SqueezeBench.RuzsaSzemeredi.f_mono
            (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]
                exact Nat.le_mul_of_pos_right 3
                  (Nat.mul_pos (Nat.pow_pos (by norm_num)) (by omega))) hle

theorem tripAux_le (fuel n : ℕ) : tripAux fuel n ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  induction fuel with
  | zero => exact tripAt_le n 0
  | succ k ih => exact max_le (tripAt_le n (k + 1)) ih

theorem cayAt_le (k : ℕ) (hk : 1 ≤ k) : cayAt k ≤ SqueezeBench.RuzsaSzemeredi.f (3 ^ k) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r ≤ 5 ∧ k = 6 * q + r :=
    ⟨k / 6, k % 6, by omega, by omega⟩
  have hsym : symB (6 * q + r) = 112 ^ q * symr r := by
    unfold symB
    have e1 : (6 * q + r) / 6 = q := by omega
    have e2 : (6 * q + r) % 6 = r := by omega
    rw [e1, e2]
  have hqr : 1 ≤ q ∨ 1 ≤ r := by omega
  have h := cay_key q r hr hqr
  unfold cayAt
  rw [hsym, pow_add]
  exact Nat.div_le_of_le_mul h

theorem cayAux_le (fuel n : ℕ) : cayAux fuel n ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    unfold cayAux
    split_ifs with h3k
    · refine max_le ?_ ih
      exact (cayAt_le (k + 1) (by omega)).trans
        (SqueezeBench.RuzsaSzemeredi.f_mono
          (by rw [SqueezeBench.RuzsaSzemeredi.nMin_eq]
              calc 3 = 3 ^ 1 := by norm_num
                _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) h3k)
    · exact ih

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f v :=
  fun n => max_le (tripAux_le _ n) (cayAux_le _ n)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.RuzsaSzemeredi.Lower.V006.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.RuzsaSzemeredi.nMin) (n₀ := 729) (by decide)
    (by decide)

end SqueezeBench.RuzsaSzemeredi.Lower.V007
