import Mathlib
import SqueezeBench.Core

/-!
# `C₄`-free subgraphs of the hypercube — `ex(Qₙ, C₄)`

`f n` is the largest number of edges in a subgraph of the `n`-dimensional hypercube `Qₙ` that
contains no `C₄`. See OEIS A245762.

`Qₙ` is `hypercube n`: its vertices are the words `Fin n → Bool`, two words adjacent when their
Hamming distance is `1`. It has `2ⁿ` vertices and `n · 2ⁿ⁻¹` edges. A subgraph is a
`G ≤ hypercube n` on the same vertex set, and "contains no `C₄`" is Mathlib's
`(cycleGraph 4).Free G`: no injective homomorphism from the 4-cycle into `G`.

Mathlib's `extremalNumber` ranges over every graph on `Fin n`, not over subgraphs of a fixed
host, so `f` is defined directly, as the same kind of supremum restricted to `G ≤ hypercube n`.
The supremum is over a `Fintype` and the empty graph always qualifies, so `f` is total.

The 4-cycles of `Qₙ` are exactly its squares: `x`, `x` with bit `i` flipped, `x` with bits
`i` and `j` flipped, `x` with bit `j` flipped, for `i ≠ j`. `free_iff_not_hasSquare` states
this for every subgraph, so a submission can argue about squares instead of graph copies.
-/

namespace SqueezeBench.HypercubeC4

open Finset SimpleGraph

/-- The `n`-dimensional hypercube: binary words of length `n`, adjacent when they differ in
exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h => by rwa [hammingDist_comm]⟩
  loopless := ⟨fun x h => by simp at h⟩

@[simp] theorem hypercube_adj {n : ℕ} {x y : Fin n → Bool} :
    (hypercube n).Adj x y ↔ hammingDist x y = 1 := Iff.rfl

instance (n : ℕ) : DecidableRel (hypercube n).Adj :=
  fun x y => decidable_of_iff (hammingDist x y = 1) Iff.rfl

/-- Smallest meaningful parameter value. At `n = 0` the cube is a single vertex and `f 0 = 0`. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

open Classical in
/-- The largest number of edges in a `C₄`-free subgraph of `hypercube n`, pinned to `0` below
`nMin`. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n < nMin then 0 else
    sup {G : SimpleGraph (Fin n → Bool) | G ≤ hypercube n ∧ (cycleGraph 4).Free G}
      (#·.edgeFinset)

/-- Lower bounds reduce to exhibiting a `C₄`-free subgraph of the cube. -/
theorem le_f_of_free {n : ℕ} {G : SimpleGraph (Fin n → Bool)} [DecidableRel G.Adj]
    (hn : nMin ≤ n) (hle : G ≤ hypercube n) (hG : (cycleGraph 4).Free G) :
    #G.edgeFinset ≤ f n := by
  classical
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  convert! @le_sup _ _ _ _
    {G : SimpleGraph (Fin n → Bool) | G ≤ hypercube n ∧ (cycleGraph 4).Free G}
    (#·.edgeFinset) G ((mem_filter_univ _).2 ⟨hle, hG⟩)

/-- Upper bounds reduce to bounding the edges of every `C₄`-free subgraph of the cube. -/
theorem f_le_of_forall_free {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj],
      G ≤ hypercube n → (cycleGraph 4).Free G → #G.edgeFinset ≤ m) : f n ≤ m := by
  classical
  rw [f, if_neg (Nat.not_lt.mpr hn), Finset.sup_le_iff]
  intro G hG
  simp only [mem_filter, mem_univ, true_and] at hG
  convert! h G hG.1 hG.2

/-- The ambient bound: a subgraph of the cube has at most as many edges as the cube. -/
theorem f_le_card_edgeFinset_hypercube (n : ℕ) : f n ≤ #(hypercube n).edgeFinset := by
  by_cases hn : nMin ≤ n
  · exact f_le_of_forall_free hn fun G _ hle _ => card_le_card (edgeFinset_mono hle)
  · rw [f, if_pos (Nat.not_le.mp hn)]
    exact Nat.zero_le _

/-! ## `C₄`-freeness as a counting condition -/

/-- No two distinct vertices have two distinct common neighbours. -/
def NoTwoCommonNeighbours {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y u v : V, x ≠ y → u ≠ v → G.Adj x u → G.Adj y u → G.Adj x v → G.Adj y v → False

/-- A graph is `C₄`-free exactly when no two distinct vertices have two distinct common
neighbours: a 4-cycle is such a pair together with its two common neighbours. -/
theorem free_cycleGraph_four_iff {V : Type*} (G : SimpleGraph V) :
    (cycleGraph 4).Free G ↔ NoTwoCommonNeighbours G := by
  constructor
  · intro hfree x y u v hxy huv hxu hyu hxv hyv
    refine hfree ?_
    rw [isContained_iff_exists_le_comap]
    have hinj : Function.Injective (![x, u, y, v]) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [G.ne_of_adj hxu, G.ne_of_adj hyu, G.ne_of_adj hxv, G.ne_of_adj hyv,
          (G.ne_of_adj hxu).symm, (G.ne_of_adj hyu).symm, (G.ne_of_adj hxv).symm,
          (G.ne_of_adj hyv).symm, hxy.symm, huv.symm]
    refine ⟨⟨![x, u, y, v], hinj⟩, ?_⟩
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [cycleGraph_adj, comap_adj] <;>
      first
        | exact hxu.symm
        | exact hyu.symm
        | exact hxv.symm
        | exact hyv.symm
        | exact absurd hab (by decide)
  · intro h hcon
    rw [isContained_iff_exists_le_comap] at hcon
    obtain ⟨e, hle⟩ := hcon
    have h01 : G.Adj (e 0) (e 1) := hle (by decide)
    have h12 : G.Adj (e 1) (e 2) := hle (by decide)
    have h23 : G.Adj (e 2) (e 3) := hle (by decide)
    have h30 : G.Adj (e 3) (e 0) := hle (by decide)
    exact h (e 0) (e 2) (e 1) (e 3) (fun hh => by simpa using e.injective hh)
      (fun hh => by simpa using e.injective hh) h01 h12.symm h30.symm h23

/-- `le_f_of_free` in elementary terms. -/
theorem le_f_of_noTwoCommonNeighbours {n : ℕ} {G : SimpleGraph (Fin n → Bool)}
    [DecidableRel G.Adj] (hn : nMin ≤ n) (hle : G ≤ hypercube n)
    (hG : NoTwoCommonNeighbours G) : #G.edgeFinset ≤ f n :=
  le_f_of_free hn hle ((free_cycleGraph_four_iff G).mpr hG)

/-- `f_le_of_forall_free` in elementary terms. -/
theorem f_le_of_forall_noTwoCommonNeighbours {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj],
      G ≤ hypercube n → NoTwoCommonNeighbours G → #G.edgeFinset ≤ m) : f n ≤ m :=
  f_le_of_forall_free hn fun G _ hle hG => h G hle ((free_cycleGraph_four_iff G).mp hG)

/-! ## The squares of the cube -/

/-- `x` with bit `i` flipped. -/
def flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

theorem flip_apply {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    flip x i j = if j = i then !x i else x j := by
  simp [flip, Function.update_apply]

@[simp] theorem flip_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : flip (flip x i) i = x := by
  funext j
  by_cases h : j = i <;> simp [flip_apply, h]

/-- Adjacency in the cube is flipping one bit. -/
theorem hypercube_adj_iff {n : ℕ} {x y : Fin n → Bool} :
    (hypercube n).Adj x y ↔ ∃ i, y = flip x i := by
  rw [hypercube_adj, hammingDist, card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, funext fun j => ?_⟩
    have hj := congrArg (j ∈ ·) hi
    simp only [mem_filter, mem_univ, true_and, mem_singleton, eq_iff_iff] at hj
    by_cases h : j = i
    · subst h; cases hx : x j <;> cases hy : y j <;> simp_all [flip_apply]
    · simp only [flip_apply, h, if_false]
      by_contra hne
      exact h (hj.mp (Ne.symm hne))
  · rintro ⟨i, rfl⟩
    refine ⟨i, ext fun j => ?_⟩
    by_cases h : j = i <;> simp [flip_apply, h]

/-- `G` contains a whole square of the cube: a word `x` and bits `i ≠ j` such that `G` has all
four edges of the cycle `x`, `x` with `i` flipped, `x` with `i` and `j` flipped, `x` with `j`
flipped. -/
def HasSquare {n : ℕ} (G : SimpleGraph (Fin n → Bool)) : Prop :=
  ∃ x i j, i ≠ j ∧ G.Adj x (flip x i) ∧ G.Adj x (flip x j) ∧
    G.Adj (flip x i) (flip (flip x i) j) ∧ G.Adj (flip x j) (flip (flip x i) j)

/-- In a subgraph of the cube, two distinct vertices with two distinct common neighbours are
opposite corners of a square. -/
theorem noTwoCommonNeighbours_iff_not_hasSquare {n : ℕ} {G : SimpleGraph (Fin n → Bool)}
    (hG : G ≤ hypercube n) : NoTwoCommonNeighbours G ↔ ¬HasSquare G := by
  constructor
  · rintro h ⟨x, i, j, hij, h1, h2, h3, h4⟩
    refine h x (flip (flip x i) j) (flip x i) (flip x j) ?_ ?_ h1 h3.symm h2 h4.symm
    · intro he
      have := congrFun he i
      simp [flip_apply, hij] at this
    · intro he
      have := congrFun he i
      simp [flip_apply, hij] at this
  · intro h x y u v hxy huv hxu hyu hxv hyv
    obtain ⟨i, rfl⟩ := hypercube_adj_iff.mp (hG hxu)
    obtain ⟨j, rfl⟩ := hypercube_adj_iff.mp (hG hxv)
    obtain ⟨k, rfl⟩ := hypercube_adj_iff.mp (hG hyu.symm)
    obtain ⟨l, hl⟩ := hypercube_adj_iff.mp (hG hyv.symm)
    have hij : i ≠ j := by rintro rfl; exact huv rfl
    have hki : k ≠ i := by rintro rfl; simp at hxy
    have hli : l = i := by
      by_contra hne
      have := congrFun hl i
      simp [flip_apply, hki.symm, hij, Ne.symm hne] at this
    subst l
    have hkj : k = j := by
      by_contra hne
      have := congrFun hl j
      simp [flip_apply, hij.symm, Ne.symm hne] at this
    subst k
    exact h ⟨x, i, j, hij, hxu, hxv, hyu.symm, hyv.symm⟩

/-- A subgraph of the cube is `C₄`-free exactly when it contains no whole square. -/
theorem free_iff_not_hasSquare {n : ℕ} {G : SimpleGraph (Fin n → Bool)}
    (hG : G ≤ hypercube n) : (cycleGraph 4).Free G ↔ ¬HasSquare G :=
  (free_cycleGraph_four_iff G).trans (noTwoCommonNeighbours_iff_not_hasSquare hG)

/-- `le_f_of_free` in terms of squares. -/
theorem le_f_of_not_hasSquare {n : ℕ} {G : SimpleGraph (Fin n → Bool)} [DecidableRel G.Adj]
    (hn : nMin ≤ n) (hle : G ≤ hypercube n) (hG : ¬HasSquare G) : #G.edgeFinset ≤ f n :=
  le_f_of_free hn hle ((free_iff_not_hasSquare hle).mpr hG)

/-- `f_le_of_forall_free` in terms of squares. -/
theorem f_le_of_forall_not_hasSquare {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj],
      G ≤ hypercube n → ¬HasSquare G → #G.edgeFinset ≤ m) : f n ≤ m :=
  f_le_of_forall_free hn fun G _ hle hG => h G hle ((free_iff_not_hasSquare hle).mp hG)

/-! ## Known values

`f` is noncomputable, so the values are cited in the README rather than checked by `decide`.
The two smallest are still provable, and they agree with A245762. -/

/-- `Q₁` is a single edge and has no square. -/
example : f 1 = 1 := by
  refine le_antisymm ((f_le_card_edgeFinset_hypercube 1).trans (by decide)) ?_
  have hG : ¬HasSquare (hypercube 1) := by
    rintro ⟨x, i, j, hij, -⟩
    exact hij (Subsingleton.elim i j)
  have hcard : #(hypercube 1).edgeFinset = 1 := by decide
  have hle := le_f_of_not_hasSquare (G := hypercube 1) (by simp) le_rfl hG
  rwa [hcard] at hle

/-- `Q₂` without the edge between `00` and `10`: the edges with a `1` in the second bit. -/
private def cubeTwoMinusEdge : SimpleGraph (Fin 2 → Bool) where
  Adj x y := (hypercube 2).Adj x y ∧ (x 1 = true ∨ y 1 = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private instance : DecidableRel cubeTwoMinusEdge.Adj := fun x y =>
  inferInstanceAs (Decidable ((hypercube 2).Adj x y ∧ (x 1 = true ∨ y 1 = true)))

/-- `Q₂` is a single square: removing any one of its four edges leaves a path, and keeping all
four keeps the square. -/
example : f 2 = 3 := by
  refine le_antisymm (f_le_of_forall_not_hasSquare (by simp) fun G _ hle hG => ?_) ?_
  · by_contra hlt
    have hsub : G.edgeFinset ⊆ (hypercube 2).edgeFinset := edgeFinset_mono hle
    have hQ : #(hypercube 2).edgeFinset = 4 := by decide
    have heq : G = hypercube 2 :=
      edgeFinset_inj.mp (eq_of_subset_of_card_le hsub (by omega))
    subst heq
    exact hG ⟨![false, false], 0, 1, by decide, hypercube_adj.2 (by decide),
      hypercube_adj.2 (by decide), hypercube_adj.2 (by decide), hypercube_adj.2 (by decide)⟩
  · have hle := le_f_of_not_hasSquare (G := cubeTwoMinusEdge) (by simp)
      (fun _ _ h => h.1) (by unfold HasSquare; decide)
    have hcard : #cubeTwoMinusEdge.edgeFinset = 3 := by decide
    rwa [hcard] at hle

end SqueezeBench.HypercubeC4
