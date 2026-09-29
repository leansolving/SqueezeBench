import Mathlib
import SqueezeBench.Core

/-!
# Graphs with no four-cycle

`f n` is the largest number of edges in a simple graph on `n` vertices containing no `C₄` as a
subgraph. Triangles are allowed — only the 4-cycle is forbidden. See OEIS A006855.

Mathlib's `SimpleGraph.extremalNumber n H` **is** this quantity at `H = cycleGraph 4`: it is the
supremum of `#G.edgeFinset` over the graphs `G` on `Fin n` with `H.Free G`, where `H.Free G`
says that no copy of `H` is contained in `G`, a copy being an injective homomorphism. Containment
is by subgraph, not induced subgraph, which is the intended reading of "contains no `C₄`".

This `f` is total by construction: the supremum is over a `Fintype` and the empty graph always
qualifies, so no nonemptiness lemma is needed.
-/

namespace SqueezeBench.ExC4

open Finset SimpleGraph

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

/-- The largest number of edges in a `C₄`-free graph on `n` vertices, pinned to `0` below `nMin`.

Noncomputable: the supremum ranges over every graph on `Fin n`, so beyond the smallest cases the
known values are cited in the README rather than checked here. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n < nMin then 0 else extremalNumber n (cycleGraph 4)

/-- Lower bounds reduce to exhibiting a `C₄`-free graph. Wraps
`card_edgeFinset_le_extremalNumber`. -/
theorem le_f_of_free {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hn : nMin ≤ n)
    (hG : (cycleGraph 4).Free G) : #G.edgeFinset ≤ f n := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  simpa using card_edgeFinset_le_extremalNumber hG

/-- Upper bounds reduce to bounding the edges of every `C₄`-free graph. Wraps
`extremalNumber_le_iff`; the instance-implicit binder matches that lemma's own shape. -/
theorem f_le_of_forall_free {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (cycleGraph 4).Free G → #G.edgeFinset ≤ m) : f n ≤ m := by
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  have key : extremalNumber (Fintype.card (Fin n)) (cycleGraph 4) ≤ m :=
    (extremalNumber_le_iff (V := Fin n) (cycleGraph 4) m).2 fun G _ hG => h G hG
  rwa [Fintype.card_fin] at key

/-- No two distinct vertices have two distinct common neighbours. -/
def NoTwoCommonNeighbours {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y u v : V, x ≠ y → u ≠ v → G.Adj x u → G.Adj y u → G.Adj x v → G.Adj y v → False

/-- Being `C₄`-free is the elementary condition a submission actually checks: a 4-cycle is
exactly a pair of distinct vertices with two distinct common neighbours. -/
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
theorem le_f_of_noTwoCommonNeighbours {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hn : nMin ≤ n) (hG : NoTwoCommonNeighbours G) : #G.edgeFinset ≤ f n :=
  le_f_of_free hn ((free_cycleGraph_four_iff G).mpr hG)

/-- `f_le_of_forall_free` in elementary terms. -/
theorem f_le_of_forall_noTwoCommonNeighbours {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      NoTwoCommonNeighbours G → #G.edgeFinset ≤ m) : f n ≤ m :=
  f_le_of_forall_free hn fun G _ hG => h G ((free_cycleGraph_four_iff G).mp hG)

/-- The ambient bound `C(n, 2)`, free from `card_edgeFinset_le_card_choose_two`. -/
theorem f_le_choose_two (n : ℕ) : f n ≤ n.choose 2 := by
  by_cases hn : nMin ≤ n
  · exact f_le_of_forall_free hn fun G _ _ => by
      simpa using card_edgeFinset_le_card_choose_two (G := G)
  · rw [f, if_pos (Nat.not_le.mp hn)]
    exact Nat.zero_le _

/-! ## Known values

`f` is noncomputable, so the values are cited in the README rather than checked by `decide`.
The two smallest are still provable, and they agree with A006855. -/

example : f 1 = 0 := by
  refine Nat.le_zero.mp (f_le_of_forall_free (by simp) fun G _ _ => ?_)
  simp [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty, Subsingleton.elim G ⊥]

/-- On three vertices the complete graph is `C₄`-free: a copy of `C₄` would inject `Fin 4`
into `Fin 3`. -/
example : f 3 = 3 := by
  refine le_antisymm (by simpa using f_le_choose_two 3) ?_
  have hfree : (cycleGraph 4).Free (⊤ : SimpleGraph (Fin 3)) := by
    rintro hcon
    rw [isContained_iff_exists_le_comap] at hcon
    obtain ⟨e, -⟩ := hcon
    have := Fintype.card_le_of_embedding e
    simp at this
  have hle := le_f_of_free (G := (⊤ : SimpleGraph (Fin 3))) (by simp) hfree
  have hcard : #(⊤ : SimpleGraph (Fin 3)).edgeFinset = 3 := by decide
  rwa [hcard] at hle

end SqueezeBench.ExC4
