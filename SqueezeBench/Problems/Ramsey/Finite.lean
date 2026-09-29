import SqueezeBench.Problems.Ramsey.Def

/-!
# The finite Ramsey theorem

Proves `WellPosed n`: for every `n` there is an `N` with `Forces N n n`, so the set
`{N | Forces N n n}` that defines `f` is nonempty.

The argument is the Erdős–Szekeres induction `R(s+1, t+1) ≤ R(s, t+1) + R(s+1, t) + 1`.
It is run on `ForcesOn`, a variant of `Forces` quantified over the vertex *type* with a
cardinality bound rather than fixed to `Fin N`. That form is what makes the induction
work: passing to the neighbourhood of a vertex is then just an application at the
subtype, with no re-indexing. Only `ForcesOn N s t → Forces N s t` is needed, and it is
immediate by taking the vertex type to be `Fin N`.

Cliques are used throughout, in `G` and in `Gᶜ`, rather than independent sets in `G`;
`Mathlib`'s independent-set API lacks the `insert` and `induce` lemmas this proof needs.
-/

namespace SqueezeBench.Ramsey

open Finset SimpleGraph

/-- `Forces`, quantified over the vertex type with a cardinality bound. -/
def ForcesOn (N s t : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    N ≤ Fintype.card V →
    (∃ S : Finset V, G.IsNClique s S) ∨ (∃ T : Finset V, Gᶜ.IsNClique t T)

theorem forces_of_forcesOn {N s t : ℕ} (h : ForcesOn N s t) : Forces N s t := by
  intro G
  exact h G (by simp)

theorem forcesOn_mono {N M s t : ℕ} (h : N ≤ M) (hF : ForcesOn N s t) : ForcesOn M s t := by
  intro V _ _ G hcard
  exact hF G (le_trans h hcard)

/-! ## Ingredients -/

/-- Taking complements commutes with restricting to a set of vertices. Applying `ForcesOn`
to `G.induce A` produces a statement about `(G.induce A)ᶜ`, which this moves to `Gᶜ`. -/
theorem induce_compl {V : Type} (G : SimpleGraph V) (A : Set V) :
    (Gᶜ).induce A = (G.induce A)ᶜ := by
  ext a b
  simp only [comap_adj, Function.Embedding.coe_subtype, compl_adj]
  exact ⟨fun h => ⟨fun hab => h.1 (congrArg _ hab), h.2⟩,
         fun h => ⟨fun hab => h.1 (Subtype.ext hab), h.2⟩⟩

/-- The neighbours and non-neighbours of `v` account for every other vertex. -/
theorem split_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card = Fintype.card V - 1 := by
  have h := G.degree_compl v
  have hlt := G.degree_lt_card_verts v
  simp only [card_neighborFinset_eq_degree] at *
  omega

/-! ## Base cases -/

/-- The empty set is a clique of size `0`. -/
theorem forcesOn_zero_left (N t : ℕ) : ForcesOn N 0 t := by
  intro V _ _ G _
  exact Or.inl ⟨∅, by simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]⟩

theorem forcesOn_zero_right (N s : ℕ) : ForcesOn N s 0 := by
  intro V _ _ G _
  exact Or.inr ⟨∅, by simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]⟩

/-- A single vertex is a clique of size `1`. -/
theorem forcesOn_one_left (t : ℕ) : ForcesOn 1 1 t := by
  intro V _ _ G hcard
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact Or.inl ⟨{v}, by simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]⟩

/-- A single vertex is a clique of size `1` in the complement too. -/
theorem forcesOn_one_right (s : ℕ) : ForcesOn 1 s 1 := by
  intro V _ _ G hcard
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact Or.inr ⟨{v}, by simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]⟩

/-! ## The inductive step -/

/-- Erdős–Szekeres. Pick a vertex `v`; one of its neighbourhood or its non-neighbourhood
is large enough to apply the corresponding hypothesis, and the clique it yields either
transfers unchanged or extends by `v`.

The bound is `M + N`, not `M + N + 1`: `v` is spent, and the remaining `card V - 1 ≥
M + N - 1` vertices already suffice to make one of the two hypotheses apply. That count
is only valid when `M + N` is positive, which is also what supplies `v`; hence `h1`. -/
theorem forcesOn_step {M N s t : ℕ} (h1 : 1 ≤ M + N)
    (hM : ForcesOn M s (t + 1)) (hN : ForcesOn N (s + 1) t) :
    ForcesOn (M + N) (s + 1) (t + 1) := by
  intro V _ _ G hcard
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsplit := split_card G v
  rcases (by omega : M ≤ (G.neighborFinset v).card ∨ N ≤ (Gᶜ.neighborFinset v).card) with hA | hB
  · have hcardA : M ≤ Fintype.card ((G.neighborFinset v : Finset V) : Set V) := by
      simp only [Finset.coe_sort_coe, Fintype.card_coe]; exact hA
    rcases hM (G.induce ((G.neighborFinset v : Finset V) : Set V)) hcardA with ⟨S, hS⟩ | ⟨T, hT⟩
    · left
      rw [isNClique_induce_iff] at hS
      refine ⟨insert v (S.map (Function.Embedding.subtype _)), hS.insert ?_⟩
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨w, _, rfl⟩ := hb
      simpa using w.2
    · right
      rw [← induce_compl, isNClique_induce_iff] at hT
      exact ⟨_, hT⟩
  · have hcardB : N ≤ Fintype.card ((Gᶜ.neighborFinset v : Finset V) : Set V) := by
      simp only [Finset.coe_sort_coe, Fintype.card_coe]; exact hB
    rcases hN (G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V)) hcardB with ⟨S, hS⟩ | ⟨T, hT⟩
    · left
      rw [isNClique_induce_iff] at hS
      exact ⟨_, hS⟩
    · right
      rw [← induce_compl, isNClique_induce_iff] at hT
      refine ⟨insert v (T.map (Function.Embedding.subtype _)), hT.insert ?_⟩
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨w, _, rfl⟩ := hb
      simpa using w.2

/-! ## The theorem -/

/-- Finite Ramsey: some `N` forces, for every pair of clique sizes. Induction on `s + t`,
which is what forces the off-diagonal statement — the two recursive calls are at
`(s, t+1)` and `(s+1, t)`. -/
theorem forcesOn_exists : ∀ s t : ℕ, ∃ N, ForcesOn N s t := by
  have key : ∀ m s t : ℕ, m = s + t → ∃ N, ForcesOn N s t := by
    intro m
    induction m with
    | zero =>
      intro s t h
      have hs : s = 0 := by omega
      subst hs
      exact ⟨0, forcesOn_zero_left 0 t⟩
    | succ m ih =>
      intro s t h
      match s with
      | 0 => exact ⟨0, forcesOn_zero_left 0 t⟩
      | s + 1 =>
        match t with
        | 0 => exact ⟨0, forcesOn_zero_right 0 (s + 1)⟩
        | t + 1 =>
          obtain ⟨M, hM⟩ := ih s (t + 1) (by omega)
          obtain ⟨N, hN⟩ := ih (s + 1) t (by omega)
          -- `M` is bumped to `M + 1` only to make the step's positivity side condition
          -- hold; the sharp count is what `Upper.lean` uses.
          exact ⟨M + 1 + N, forcesOn_step (by omega) (forcesOn_mono (Nat.le_succ M) hM) hN⟩
  intro s t
  exact key (s + t) s t rfl

theorem forces_exists (s t : ℕ) : ∃ N, Forces N s t := by
  obtain ⟨N, hN⟩ := forcesOn_exists s t
  exact ⟨N, forces_of_forcesOn hN⟩

/-- `f` is well posed: the set it takes the infimum of is nonempty. -/
theorem wellPosed (n : ℕ) : WellPosed n := forces_exists n n

/-- Lower bounds on `f` reduce to a lower bound on every `N` that forces. Unconditional,
unlike `le_f_of_wellPosed`, because well-posedness is now proved. -/
theorem le_f {n a : ℕ} (hn : nMin ≤ n) (h : ∀ N, Forces N n n → a ≤ N) : a ≤ f n :=
  le_f_of_wellPosed hn (wellPosed n) h

/-! ## The theorem, quantitatively

`forcesOn_exists` says *some* `N` forces; the rest of this file tracks which one. The
induction is the same, run with the vertex count carried explicitly, so the two recursive
calls contribute `C(s+t+1, s)` and `C(s+t+1, s+1)` and Pascal's rule collapses their sum to
`C(s+t+2, s+1)`.

Both clique sizes are written as successors, which keeps every index a sum and so keeps
natural subtraction out of the induction. It appears only in `forces_choose`, where the
bound is phrased in terms of `n` rather than `n - 1`. -/

/-- Erdős–Szekeres, quantitative: `C(s+t, s)` vertices force a clique of size `s+1` or a
clique of size `t+1` in the complement. -/
theorem forcesOn_choose : ∀ s t : ℕ, ForcesOn (Nat.choose (s + t) s) (s + 1) (t + 1) := by
  have key : ∀ m s t : ℕ, m = s + t → ForcesOn (Nat.choose (s + t) s) (s + 1) (t + 1) := by
    intro m
    induction m with
    | zero =>
      intro s t h
      have hs : s = 0 := by omega
      have ht : t = 0 := by omega
      subst hs; subst ht
      apply forcesOn_one_left
    | succ m ih =>
      intro s t h
      match s with
      | 0 =>
        simp only [Nat.choose_zero_right, Nat.zero_add]
        apply forcesOn_one_left
      | s + 1 =>
        match t with
        | 0 =>
          rw [Nat.add_zero, Nat.choose_self]
          apply forcesOn_one_right
        | t + 1 =>
          have hM : ForcesOn (Nat.choose (s + t + 1) s) (s + 1) (t + 1 + 1) := by
            have hih : ForcesOn (Nat.choose (s + (t + 1)) s) (s + 1) (t + 1 + 1) :=
              ih s (t + 1) (by omega)
            rwa [show s + (t + 1) = s + t + 1 from by omega] at hih
          have hN : ForcesOn (Nat.choose (s + t + 1) (s + 1)) (s + 1 + 1) (t + 1) := by
            have hih : ForcesOn (Nat.choose (s + 1 + t) (s + 1)) (s + 1 + 1) (t + 1) :=
              ih (s + 1) t (by omega)
            rwa [show s + 1 + t = s + t + 1 from by omega] at hih
          have h1 : 1 ≤ Nat.choose (s + t + 1) s + Nat.choose (s + t + 1) (s + 1) := by
            have hle : s ≤ s + t + 1 := by omega
            have := Nat.choose_pos hle
            omega
          have hpascal : Nat.choose (s + 1 + (t + 1)) (s + 1)
              = Nat.choose (s + t + 1) s + Nat.choose (s + t + 1) (s + 1) := by
            rw [show s + 1 + (t + 1) = s + t + 1 + 1 from by omega, Nat.choose_succ_succ']
          rw [hpascal]
          intro V _ _
          exact forcesOn_step h1 hM hN
  intro s t
  exact key (s + t) s t rfl

/-- The diagonal case, stated in terms of `n`. -/
theorem forces_choose (n : ℕ) : Forces (Nat.choose (2 * n - 2) (n - 1)) n n := by
  match n with
  | 0 => simpa using forces_of_forcesOn (forcesOn_zero_left 1 0)
  | m + 1 =>
    rw [show 2 * (m + 1) - 2 = m + m from by omega, show m + 1 - 1 = m from by omega]
    exact forces_of_forcesOn (forcesOn_choose m m)

end SqueezeBench.Ramsey
