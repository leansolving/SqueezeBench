import SqueezeBench.Problems.Schur.Def

/-!
# Well-posedness for the Schur problem

Proves `WellPosed k`: for every `k ≥ nMin` there is an `N` with `Forces k N`, so the set
`{N | Forces k N}` that defines `f` is nonempty.

Schur's theorem follows from the `k`-colour Ramsey number for triangles. The Ramsey
development in `SqueezeBench.Problems.Ramsey` is two-colour by construction — `Forces`
is phrased with `G` and `Gᶜ` — so the triangle case is proved here directly instead, by
pigeonhole on the edges at a single vertex. That is both shorter than generalising the
graph development and gives the far better bound `R_k(3) ≤ 3·k!`.

The reduction is the classical one: colour the edge `{i, j}` of `K_N` by the colour of
`|i - j|`; a monochromatic triangle `v₀ < v₁ < v₂` gives `x = v₁ - v₀`, `y = v₂ - v₁`,
`z = v₂ - v₀` with `x + y = z`, all of one colour.
-/

namespace SqueezeBench.Schur

open Finset

/-! ## Monochromatic triangles for `k` colours -/

/-- Every symmetric `k`-colouring of the pairs from at least `N` points has a
monochromatic triple. -/
def MonoTriangle (N k : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (col : V → V → Fin k),
    (∀ a b, col a b = col b a) → N ≤ Fintype.card V →
    ∃ (i : Fin k) (S : Finset V), S.card = 3 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col a b = i

theorem monoTriangle_mono {N M k : ℕ} (hNM : N ≤ M) (h : MonoTriangle N k) :
    MonoTriangle M k := by
  intro V _ _ col hsym hcard
  exact h col hsym (le_trans hNM hcard)

/-- With one colour every triple is monochromatic. -/
theorem monoTriangle_one : MonoTriangle 3 1 := by
  intro V _ _ col _ hcard
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (Finset.univ : Finset V).card by simpa using hcard)
  exact ⟨0, S, hS, fun _ _ _ _ _ => Subsingleton.elim _ _⟩

/-- Pigeonhole at a vertex: one colour class of its incident edges is large, and either it
contains an edge of the same colour — closing a triangle — or it uses one colour fewer. -/
theorem monoTriangle_step {N k : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) (h : MonoTriangle N k) :
    MonoTriangle ((k + 1) * (N - 1) + 2) (k + 1) := by
  classical
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  intro V _ _ col hsym hcard
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  set s : Finset V := Finset.univ.erase v with hs
  have hscard : s.card = Fintype.card V - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  have hmaps : ∀ a ∈ s, col v a ∈ (Finset.univ : Finset (Fin (k + 1))) :=
    fun _ _ => Finset.mem_univ _
  have hlt : (Finset.univ : Finset (Fin (k + 1))).card * (N - 1) < s.card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set W : Finset V := s.filter (fun a => col v a = c) with hW
  have hWcard : N ≤ W.card := by omega
  have hWv : ∀ a ∈ W, col v a = c ∧ a ≠ v := by
    intro a ha
    rw [hW, Finset.mem_filter, hs, Finset.mem_erase] at ha
    exact ⟨ha.2, ha.1.1⟩
  by_cases hpair : ∃ a ∈ W, ∃ b ∈ W, a ≠ b ∧ col a b = c
  · obtain ⟨a, ha, b, hb, hab, hcab⟩ := hpair
    have hva : v ≠ a := fun he => (hWv a ha).2 he.symm
    have hvb : v ≠ b := fun he => (hWv b hb).2 he.symm
    refine ⟨c, {v, a, b}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hva, hvb]),
        Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    · intro p hp q hq hpq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;>
        first
          | exact absurd rfl hpq
          | exact (hWv a ha).1
          | exact (hWv b hb).1
          | exact hcab
          | (rw [hsym]
             first
               | exact (hWv a ha).1
               | exact (hWv b hb).1
               | exact hcab)
  · have hne : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → col a b ≠ c := by
      intro a ha b hb hab hcc
      exact hpair ⟨a, ha, b, hb, hab, hcc⟩
    set col' : ↥W → ↥W → Fin k :=
      fun a b => Function.invFun (Fin.succAbove c) (col ↑a ↑b) with hcol'
    have hsym' : ∀ a b : ↥W, col' a b = col' b a := by
      intro a b
      simp only [hcol', hsym ↑a ↑b]
    have hWtype : N ≤ Fintype.card ↥W := by rwa [Fintype.card_coe]
    obtain ⟨ι, S', hS'card, hS'mono⟩ := h col' hsym' hWtype
    refine ⟨Fin.succAbove c ι, S'.map (Function.Embedding.subtype _), ?_, ?_⟩
    · rw [Finset.card_map]; exact hS'card
    · intro p hp q hq hpq
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hp hq
      obtain ⟨a, ha, rfl⟩ := hp
      obtain ⟨b, hb, rfl⟩ := hq
      have hab : a ≠ b := fun he => hpq (by rw [he])
      have hexists : ∃ z, Fin.succAbove c z = col ↑a ↑b :=
        Fin.exists_succAbove_eq (hne ↑a a.2 ↑b b.2 (by simpa using hpq))
      have heq := Function.invFun_eq hexists
      have hdef : col' a b = Function.invFun (Fin.succAbove c) (col ↑a ↑b) := rfl
      rw [← hdef, hS'mono a ha b hb hab] at heq
      exact heq.symm

/-- `3*k!` points force a monochromatic triangle in `k` colours. -/
theorem monoTriangle_factorial : ∀ k : ℕ, MonoTriangle (3 * Nat.factorial (k + 1)) (k + 1) := by
  intro k
  induction k with
  | zero =>
    have h3 : 3 * Nat.factorial (0 + 1) = 3 := by decide
    rw [h3]
    intro V _ _ col hsym hcard
    exact monoTriangle_one col hsym hcard
  | succ k ih =>
    refine monoTriangle_mono ?_ (monoTriangle_step (by omega) ?_ ih)
    · have hfac : Nat.factorial (k + 2) = (k + 2) * Nat.factorial (k + 1) :=
        Nat.factorial_succ (k + 1)
      have hpos : 0 < Nat.factorial (k + 1) := Nat.factorial_pos (k + 1)
      obtain ⟨G, hG⟩ : ∃ G, 3 * Nat.factorial (k + 1) = G + 1 :=
        ⟨3 * Nat.factorial (k + 1) - 1, by omega⟩
      have hR : 3 * ((k + 2) * Nat.factorial (k + 1)) = (k + 2) * G + (k + 2) := by
        rw [show (k + 2) * G + (k + 2) = (k + 2) * (G + 1) from by ring, ← hG]
        ring
      have hL : (k + 1 + 1) * (3 * Nat.factorial (k + 1) - 1) + 2 = (k + 2) * G + 2 := by
        rw [hG, Nat.add_sub_cancel, show k + 1 + 1 = k + 2 from rfl]
      rw [hfac, hL, hR]
      omega
    · have hpos : 0 < Nat.factorial (k + 1) := Nat.factorial_pos (k + 1)
      omega

/-! ## Schur's theorem -/

/-- The distance between two vertices, as a natural number. -/
def gap {K : ℕ} (a b : Fin K) : ℕ := max (a : ℕ) (b : ℕ) - min (a : ℕ) (b : ℕ)

theorem gap_comm {K : ℕ} (a b : Fin K) : gap a b = gap b a := by
  simp [gap, max_comm, min_comm]

theorem gap_of_lt {K : ℕ} {a b : Fin K} (h : (a : ℕ) < (b : ℕ)) :
    gap a b = (b : ℕ) - (a : ℕ) := by
  simp only [gap, max_eq_right (le_of_lt h), min_eq_left (le_of_lt h)]

/-- Colouring the pair `{a, b}` by the colour of the gap turns a monochromatic triangle
into a monochromatic solution of `x + y = z`. -/
theorem forces_factorial {k : ℕ} (hk : nMin ≤ k) :
    Forces k (3 * Nat.factorial k - 1) := by
  have hk1 : 1 ≤ k := by simpa [nMin] using hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hfp : 0 < Nat.factorial (j + 1) := Nat.factorial_pos _
  obtain ⟨N, hN⟩ : ∃ N, 3 * Nat.factorial (j + 1) = N + 1 :=
    ⟨3 * Nat.factorial (j + 1) - 1, by omega⟩
  rw [hN, Nat.add_sub_cancel]
  intro c
  have hcard : 3 * Nat.factorial (j + 1) ≤ Fintype.card (Fin (N + 1)) := by
    simp only [Fintype.card_fin]; omega
  have hsymc : ∀ a b : Fin (N + 1), c (gap a b) = c (gap b a) := by
    intro a b; rw [gap_comm]
  obtain ⟨ι, S, hScard, hSmono⟩ :=
    monoTriangle_factorial j (fun a b : Fin (N + 1) => c (gap a b)) hsymc hcard
  set w : Fin 3 → Fin (N + 1) := fun i => (S.orderIsoOfFin hScard i : Fin (N + 1)) with hw
  have hwmem : ∀ i, w i ∈ S := fun i => (S.orderIsoOfFin hScard i).2
  have hwlt : ∀ i j : Fin 3, i < j → (w i : ℕ) < (w j : ℕ) := by
    intro i j hij
    have h : (S.orderIsoOfFin hScard i : Fin (N + 1)) < (S.orderIsoOfFin hScard j) := by
      exact_mod_cast (S.orderIsoOfFin hScard).lt_iff_lt.mpr hij
    exact h
  have hwne : ∀ i j : Fin 3, i < j → w i ≠ w j := by
    intro i j hij he
    exact absurd (congrArg (fun z : Fin (N + 1) => (z : ℕ)) he) (Nat.ne_of_lt (hwlt i j hij))
  have hcol : ∀ i j : Fin 3, i < j → c ((w j : ℕ) - (w i : ℕ)) = ι := by
    intro i j hij
    have h := hSmono _ (hwmem i) _ (hwmem j) (hwne i j hij)
    rwa [gap_of_lt (hwlt i j hij)] at h
  have hb : ∀ i : Fin 3, (w i : ℕ) ≤ N := fun i => Nat.lt_succ_iff.mp (w i).isLt
  have h01 := hwlt 0 1 (by decide)
  have h12 := hwlt 1 2 (by decide)
  have h02 := hwlt 0 2 (by decide)
  refine ⟨(w 1 : ℕ) - (w 0 : ℕ), ?_, (w 2 : ℕ) - (w 1 : ℕ), ?_,
    (w 2 : ℕ) - (w 0 : ℕ), ?_, ?_, ?_, ?_⟩
  · rw [mem_Icc]; have := hb 1; omega
  · rw [mem_Icc]; have := hb 2; omega
  · rw [mem_Icc]; have := hb 2; omega
  · omega
  · rw [hcol 0 1 (by decide), hcol 1 2 (by decide)]
  · rw [hcol 1 2 (by decide), hcol 0 2 (by decide)]

/-- `f` is well posed above `nMin`: the set it takes the infimum of is nonempty. -/
theorem wellPosed {k : ℕ} (hk : nMin ≤ k) : WellPosed k :=
  ⟨_, forces_factorial hk⟩

/-- Lower bounds on `f` reduce to a lower bound on every `N` that forces. Unconditional,
unlike `le_f_of_wellPosed`, because well-posedness is now proved. -/
theorem le_f {k a : ℕ} (hk : nMin ≤ k) (h : ∀ N, Forces k N → a + 1 ≤ N) : a ≤ f k :=
  le_f_of_wellPosed hk (wellPosed hk) h

end SqueezeBench.Schur
