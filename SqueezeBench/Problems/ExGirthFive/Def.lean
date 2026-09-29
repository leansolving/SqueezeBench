import Mathlib
import SqueezeBench.Core

/-!
# Graphs of girth at least five

`f n` is the largest number of edges in a simple graph on `n` vertices whose girth is at least
`5` — equivalently, containing neither a triangle nor a 4-cycle. See OEIS A006856.

The condition is `5 ≤ G.egirth`, Mathlib's *extended* girth, which is `⊤` on an acyclic graph.
The ℕ-valued `SimpleGraph.girth` would not do: it is `0` on an acyclic graph, so the empty graph
would fail the condition and the supremum below could be empty.

This `f` is total by construction: the supremum is over a `Fintype` and the empty graph always
qualifies, so no nonemptiness lemma is needed.
-/

namespace SqueezeBench.ExGirthFive

open Finset SimpleGraph

/-- Smallest meaningful parameter value. -/
def nMin : ℕ := 1

@[simp] theorem nMin_eq : nMin = 1 := rfl

open Classical in
/-- The largest number of edges in a graph of girth at least `5` on `n` vertices, pinned to `0`
below `nMin`.

Noncomputable: the supremum ranges over every graph on `Fin n`, so beyond the smallest cases the
known values are cited in the README rather than checked here. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n < nMin then 0 else
    (univ.filter fun G : SimpleGraph (Fin n) => 5 ≤ G.egirth).sup (fun G => #G.edgeFinset)

/-- Lower bounds reduce to exhibiting a graph of girth at least `5`. -/
theorem le_f_of_egirth {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hn : nMin ≤ n)
    (hG : 5 ≤ G.egirth) : #G.edgeFinset ≤ f n := by
  classical
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  have hmem : G ∈ univ.filter fun G : SimpleGraph (Fin n) => 5 ≤ G.egirth := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hG
  convert! Finset.le_sup (f := fun G : SimpleGraph (Fin n) => #G.edgeFinset) hmem

/-- Upper bounds reduce to bounding the edges of every graph of girth at least `5`. -/
theorem f_le_of_forall_egirth {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      5 ≤ G.egirth → #G.edgeFinset ≤ m) : f n ≤ m := by
  classical
  rw [f, if_neg (Nat.not_lt.mpr hn)]
  refine Finset.sup_le fun G hG => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
  exact h G hG

/-- No two distinct vertices have two distinct common neighbours. -/
def NoTwoCommonNeighbours {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y u v : V, x ≠ y → u ≠ v → G.Adj x u → G.Adj y u → G.Adj x v → G.Adj y v → False

/-- Girth at least `5` is the elementary condition a submission actually checks: no triangle,
and no pair of distinct vertices with two distinct common neighbours. -/
theorem five_le_egirth_iff {V : Type*} (G : SimpleGraph V) :
    5 ≤ G.egirth ↔ G.CliqueFree 3 ∧ NoTwoCommonNeighbours G := by
  constructor
  · refine fun h => ⟨fun s hs => ?_, fun x y u v hxy huv hxu hyu hxv hyv => ?_⟩
    · obtain ⟨a, w, hw, hlen⟩ := is3Clique_iff_exists_cycle_length_three.mp ⟨s, hs⟩
      have hle := le_egirth.mp h a w hw
      rw [hlen] at hle
      norm_num at hle
    · have hw : (Walk.cons hxu (Walk.cons hyu.symm
          (Walk.cons hyv (Walk.cons hxv.symm Walk.nil)))).IsCycle := by
        simp only [Walk.isCycle_def]
        refine ⟨?_, ?_, ?_⟩ <;> aesop
      have hle := le_egirth.mp h x _ hw
      simp only [Walk.length_cons, Walk.length_nil] at hle
      norm_num at hle
  · rintro ⟨hcf, hnt⟩
    rw [le_egirth]
    intro a w hw
    have hlen : 5 ≤ w.length := by
      by_contra hlt
      rw [Nat.not_le] at hlt
      have h3 := hw.three_le_length
      match w, hw with
      | .cons _ (.cons _ (.cons _ .nil)), hw =>
          exact hcf _ (is3Clique_iff_exists_cycle_length_three.mpr
            ⟨a, _, hw, by simp⟩).choose_spec
      | .cons h1 (.cons h2 (.cons h3' (.cons h4 .nil))), hw =>
          simp only [Walk.isCycle_def, Walk.isTrail_def, Walk.support_cons, Walk.support_nil,
            List.tail_cons, List.nodup_cons, List.mem_cons, List.not_mem_nil] at hw
          exact hnt _ _ _ _ (by aesop) (by aesop) h1 h2.symm h4.symm h3'
      | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))), _ =>
          simp only [Walk.length_cons] at hlt
          omega
    exact_mod_cast hlen

/-- `le_f_of_egirth` in elementary terms. -/
theorem le_f_of_cliqueFree_of_noTwoCommonNeighbours {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hn : nMin ≤ n) (h3 : G.CliqueFree 3)
    (h4 : NoTwoCommonNeighbours G) : #G.edgeFinset ≤ f n :=
  le_f_of_egirth hn ((five_le_egirth_iff G).mpr ⟨h3, h4⟩)

/-- `f_le_of_forall_egirth` in elementary terms. -/
theorem f_le_of_forall_cliqueFree_noTwoCommonNeighbours {n m : ℕ} (hn : nMin ≤ n)
    (h : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.CliqueFree 3 → NoTwoCommonNeighbours G → #G.edgeFinset ≤ m) : f n ≤ m :=
  f_le_of_forall_egirth hn fun G _ hG =>
    h G ((five_le_egirth_iff G).mp hG).1 ((five_le_egirth_iff G).mp hG).2

/-- The ambient bound `C(n, 2)`, free from `card_edgeFinset_le_card_choose_two`. -/
theorem f_le_choose_two (n : ℕ) : f n ≤ n.choose 2 := by
  by_cases hn : nMin ≤ n
  · exact f_le_of_forall_egirth hn fun G _ _ => by
      simpa using card_edgeFinset_le_card_choose_two (G := G)
  · rw [f, if_pos (Nat.not_le.mp hn)]
    exact Nat.zero_le _

/-! ## Known values

`f` is noncomputable, so the values are cited in the README rather than checked by `decide`.
These two are still provable, and they agree with A006856. -/

example : f 1 = 0 := by
  refine Nat.le_zero.mp (f_le_of_forall_egirth (by simp) fun G _ _ => ?_)
  simp [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty, Subsingleton.elim G ⊥]

/-- Half of `f 3 = 2`: the girth condition rules out the triangle, so Mantel's bound applies.
The matching lower half needs an explicit two-edge graph, and arrives with the seed record. -/
example : f 3 ≤ 2 := by
  refine f_le_of_forall_egirth (by simp) fun G _ hG => ?_
  have h3 := ((five_le_egirth_iff G).mp hG).1
  simpa using h3.card_edgeFinset_le (r := 2)

end SqueezeBench.ExGirthFive
