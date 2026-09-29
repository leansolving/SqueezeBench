import SqueezeBench.Problems.HypercubeC4.Records.Lower.V007.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V006.Proof

-- The block step's square-freeness proof and the size-4 template derive from Erdos86.lean (JSP-000102, https://github.com/baobingzhang/jsp-000102-erdos86-lean), Apache License 2.0 (LICENSES/Apache-2.0.txt), via V006; modified.

/-! Record V007 for HypercubeC4, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V007.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V007

open Finset SimpleGraph
open V006 hiding blk proj restPar blk_fl_self blk_fl_of_ne proj_fl restPar_fl_self
  restPar_fl_of_ne card_filter_prod

/-! ### Templates: `e/o/a`-colourings of `Q_k` in which every square meets `e` and `o` -/

-- A template on `Q_k`: two disjoint edge classes `e`, `o`, each well defined on edges, every
-- square containing an edge of each; and, per direction `j` and parity class, the numbers of
-- vertices whose `j`-edge is in `e`, in `o`, in neither.
structure Tmpl (k : ℕ) where
  isE : (Fin k → Bool) → Fin k → Bool
  isO : (Fin k → Bool) → Fin k → Bool
  isE_fl : ∀ v j, isE (fl v j) j = isE v j
  isO_fl : ∀ v j, isO (fl v j) j = isO v j
  disj : ∀ v j, ¬ (isE v j = true ∧ isO v j = true)
  sqE : ∀ v j j', j ≠ j' →
    isE v j = true ∨ isE v j' = true ∨ isE (fl v j') j = true ∨ isE (fl v j) j' = true
  sqO : ∀ v j j', j ≠ j' →
    isO v j = true ∨ isO v j' = true ∨ isO (fl v j') j = true ∨ isO (fl v j) j' = true
  e : Fin k → ℕ
  o : Fin k → ℕ
  a : Fin k → ℕ
  cntE : ∀ j β, #{v | oddOn univ v = β ∧ isE v j = true} = e j
  cntO : ∀ j β, #{v | oddOn univ v = β ∧ isO v j = true} = o j
  cntA : ∀ j β, #{v | oddOn univ v = β ∧ isE v j = false ∧ isO v j = false} = a j

-- The colour of the template edge at `v` in direction `j`: `π` on `e`, `!π` on `o`, `c` on `a`.
def tcol {k : ℕ} (T : Tmpl k) (v : Fin k → Bool) (j : Fin k) (c π : Bool) : Bool :=
  if T.isE v j then π else if T.isO v j then !π else c

section TcolLemmas

variable {k : ℕ} (T : Tmpl k)

theorem tcol_fl (v : Fin k → Bool) (j : Fin k) (c π : Bool) :
    tcol T (fl v j) j c π = tcol T v j c π := by
  unfold tcol
  rw [T.isE_fl, T.isO_fl]

theorem tcol_of_e {v : Fin k → Bool} {j : Fin k} (h : T.isE v j = true) (c π : Bool) :
    tcol T v j c π = π := by
  simp [tcol, h]

theorem tcol_of_o {v : Fin k → Bool} {j : Fin k} (h : T.isO v j = true) (c π : Bool) :
    tcol T v j c π = !π := by
  have hne : T.isE v j = false := by
    cases he : T.isE v j
    · rfl
    · exact absurd ⟨he, h⟩ (T.disj v j)
  simp [tcol, hne, h]

theorem tcol_of_a {v : Fin k → Bool} {j : Fin k} (h : ¬ (T.isE v j = true ∨ T.isO v j = true))
    (c π : Bool) : tcol T v j c π = c := by
  rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at h
  simp [tcol, h.1, h.2]

theorem tcol_ne_of_matched {v : Fin k → Bool} {j : Fin k}
    (h : T.isE v j = true ∨ T.isO v j = true) (c c' π : Bool) :
    tcol T v j c π ≠ tcol T v j c' (!π) := by
  rcases h with h | h
  · rw [tcol_of_e T h, tcol_of_e T h]; cases π <;> simp
  · rw [tcol_of_o T h, tcol_of_o T h]; cases π <;> simp

-- A square of the template, all four edges coloured with the same `c, π`, is never all `true`.
theorem tcol_square (v : Fin k → Bool) {j j' : Fin k} (hjj : j ≠ j') (c π : Bool) :
    ¬ (tcol T v j c π = true ∧ tcol T (fl v j') j c π = true ∧
      tcol T v j' c π = true ∧ tcol T (fl v j) j' c π = true) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hπ : π = true := by
    rcases T.sqE v j j' hjj with h | h | h | h
    · rw [tcol_of_e T h] at h1; exact h1
    · rw [tcol_of_e T h] at h3; exact h3
    · rw [tcol_of_e T h] at h2; exact h2
    · rw [tcol_of_e T h] at h4; exact h4
  have hπ' : (!π) = true := by
    rcases T.sqO v j j' hjj with h | h | h | h
    · rw [tcol_of_o T h] at h1; exact h1
    · rw [tcol_of_o T h] at h3; exact h3
    · rw [tcol_of_o T h] at h2; exact h2
    · rw [tcol_of_o T h] at h4; exact h4
  rw [hπ] at hπ'
  exact Bool.false_ne_true hπ'

end TcolLemmas

/-! ### The four templates -/

-- Size 4: V006's `e`/`o` matchings.
def T4 : Tmpl 4 where
  isE v j := decide (eD v = j)
  isO v j := decide (oD v = j)
  isE_fl v j := decide_eq_decide.mpr (eD_fl v j)
  isO_fl v j := decide_eq_decide.mpr (oD_fl v j)
  disj v j := by
    simp only [decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    exact eD_ne_oD v (h1.trans h2.symm)
  sqE v j j' h := by simpa only [decide_eq_true_eq] using hasE v j j' h
  sqO v j j' h := by simpa only [decide_eq_true_eq] using hasO v j j' h
  e _ := 2
  o _ := 2
  a _ := 4
  cntE := by decide
  cntO := by decide
  cntA := by decide

-- Size 3: `e = {*00, 0*1, 11*}`, `o = {*10, 1*1, 00*}` (bits `v 0 v 1 v 2`, `*` the direction).
def isE3 (v : Fin 3 → Bool) (j : Fin 3) : Bool :=
  if j = 0 then !v 1 && !v 2 else if j = 1 then !v 0 && v 2 else v 0 && v 1

def isO3 (v : Fin 3 → Bool) (j : Fin 3) : Bool :=
  if j = 0 then v 1 && !v 2 else if j = 1 then v 0 && v 2 else !v 0 && !v 1

def T3 : Tmpl 3 where
  isE := isE3
  isO := isO3
  isE_fl := by decide
  isO_fl := by decide
  disj := by decide
  sqE := by decide
  sqO := by decide
  e _ := 1
  o _ := 1
  a _ := 2
  cntE := by decide
  cntO := by decide
  cntA := by decide

-- Size 2: `e = {*0}`, `o = {*1}`; the second direction is all `a`.
def T2 : Tmpl 2 where
  isE v j := j = 0 && !v 1
  isO v j := j = 0 && v 1
  isE_fl := by decide
  isO_fl := by decide
  disj := by decide
  sqE := by decide
  sqO := by decide
  e j := if j = 0 then 1 else 0
  o j := if j = 0 then 1 else 0
  a j := if j = 0 then 0 else 2
  cntE := by decide
  cntO := by decide
  cntA := by decide

-- Size 1: the single edge is an `a`-edge.
def T1 : Tmpl 1 where
  isE _ _ := false
  isO _ _ := false
  isE_fl _ _ := rfl
  isO_fl _ _ := rfl
  disj _ _ h := Bool.false_ne_true h.1
  sqE _ j j' h := absurd (Subsingleton.elim j j') h
  sqO _ j j' h := absurd (Subsingleton.elim j j') h
  e _ := 0
  o _ := 0
  a _ := 1
  cntE := by decide
  cntO := by decide
  cntA := by decide

/-! ### The block step `Q_ι → Q_{Σ w, Fin (b w)}` -/

section Step

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {b : ι → ℕ}

-- The block of `X` at `w`, a vertex of `Q_{b w}`.
def sblk (X : (Σ w, Fin (b w)) → Bool) (w : ι) : Fin (b w) → Bool := fun j => X ⟨w, j⟩

-- The block parities of `X`, a vertex of `Q_ι`.
def sproj (X : (Σ w, Fin (b w)) → Bool) : ι → Bool := fun w => oddOn univ (sblk X w)

-- The parity of `X` outside the block `w`.
def stau (X : (Σ w, Fin (b w)) → Bool) (w : ι) : Bool :=
  oddOn (univ.filter fun p : Σ w, Fin (b w) => p.1 ≠ w) X

omit [Fintype ι] in
theorem sblk_fl_self (X : (Σ w, Fin (b w)) → Bool) (w : ι) (j : Fin (b w)) :
    sblk (fl X ⟨w, j⟩) w = fl (sblk X w) j := by
  funext k
  by_cases h : k = j
  · subst h; simp [sblk, fl]
  · have : (⟨w, k⟩ : Σ w, Fin (b w)) ≠ ⟨w, j⟩ := fun e => h (eq_of_heq (Sigma.mk.inj_iff.mp e).2)
    simp [sblk, fl, h, this]

omit [Fintype ι] in
theorem sblk_fl_of_ne (X : (Σ w, Fin (b w)) → Bool) {w w' : ι} (h : w' ≠ w) (j : Fin (b w')) :
    sblk (fl X ⟨w', j⟩) w = sblk X w := by
  funext k
  have : (⟨w, k⟩ : Σ w, Fin (b w)) ≠ ⟨w', j⟩ := fun e => h (congrArg Sigma.fst e).symm
  simp [sblk, fl, this]

omit [Fintype ι] in
theorem sproj_fl (X : (Σ w, Fin (b w)) → Bool) (w : ι) (j : Fin (b w)) :
    sproj (fl X ⟨w, j⟩) = fl (sproj X) w := by
  funext w'
  by_cases h : w' = w
  · subst h
    rw [fl_self, sproj, sproj, sblk_fl_self, oddOn_fl_of_mem _ (mem_univ _)]
  · rw [fl_of_ne _ h, sproj, sproj, sblk_fl_of_ne X (Ne.symm h)]

theorem stau_fl_self (X : (Σ w, Fin (b w)) → Bool) (w : ι) (j : Fin (b w)) :
    stau (fl X ⟨w, j⟩) w = stau X w :=
  oddOn_fl_of_notMem X (by simp)

theorem stau_fl_of_ne (X : (Σ w, Fin (b w)) → Bool) {w w' : ι} (h : w' ≠ w) (j : Fin (b w')) :
    stau (fl X ⟨w', j⟩) w = !stau X w :=
  oddOn_fl_of_mem X (by simpa using h)

-- The colour of the edge of `Q_{Σ w, Fin (b w)}` at `X` in direction `⟨w, j⟩`.
def bcol (T : ∀ w, Tmpl (b w)) (C : Col ι) (X : (Σ w, Fin (b w)) → Bool)
    (p : Σ w, Fin (b w)) : Bool :=
  tcol (T p.1) (sblk X p.1) p.2 (C.col (sproj X) p.1) (stau X p.1)

-- The block step: inside block `w`, an `e`-edge of the template is coloured by the parity of `X`
-- outside the block, an `o`-edge by the opposite parity, an `a`-edge by the colour of the
-- `w`-edge of `Q_ι` at the vector of block parities.
def bstep (T : ∀ w, Tmpl (b w)) (C : Col ι) : Col (Σ w, Fin (b w)) where
  col := bcol T C
  col_fl X p := by
    obtain ⟨w, j⟩ := p
    simp only [bcol]
    rw [sblk_fl_self, sproj_fl, C.col_fl, stau_fl_self, tcol_fl]
  noSq X p q hpq := by
    obtain ⟨w, j⟩ := p
    obtain ⟨w', k⟩ := q
    simp only [bcol]
    by_cases hw : w = w'
    · subst hw
      have hjk : j ≠ k := fun h => hpq (by rw [h])
      rw [sblk_fl_self, sblk_fl_self, sproj_fl, sproj_fl, C.col_fl, stau_fl_self, stau_fl_self]
      exact tcol_square _ _ hjk _ _
    · rw [sblk_fl_of_ne X (Ne.symm hw), sblk_fl_of_ne X hw, sproj_fl, sproj_fl,
        stau_fl_of_ne X (Ne.symm hw), stau_fl_of_ne X hw]
      rintro ⟨h1, h2, h3, h4⟩
      by_cases hA : (T w).isE (sblk X w) j = true ∨ (T w).isO (sblk X w) j = true
      · exact tcol_ne_of_matched _ hA _ _ _ (h1.trans h2.symm)
      by_cases hB : (T w').isE (sblk X w') k = true ∨ (T w').isO (sblk X w') k = true
      · exact tcol_ne_of_matched _ hB _ _ _ (h3.trans h4.symm)
      rw [tcol_of_a _ hA] at h1 h2
      rw [tcol_of_a _ hB] at h3 h4
      exact C.noSq (sproj X) w w' hw ⟨h1, h2, h3, h4⟩

end Step


/-! ### Counting -/

section Halving

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- Flipping a coordinate of `S` toggles `oddOn S`, so each parity class is half of the cube.
theorem two_mul_card_oddOn_of_mem {S : Finset ι} {i : ι} (hi : i ∈ S) (β : Bool) :
    2 * #{x : ι → Bool | oddOn S x = β} = 2 ^ Fintype.card ι := by
  have hswap : #{x : ι → Bool | oddOn S x = β} = #{x : ι → Bool | ¬ oddOn S x = β} := by
    refine Finset.card_nbij' (fl · i) (fl · i) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      rw [oddOn_fl_of_mem x hi, hx]
      cases β <;> simp
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      rw [oddOn_fl_of_mem x hi]
      cases h : oddOn S x <;> cases β <;> simp_all
    · intro x _; simp
    · intro x _; simp
  have htot := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (ι → Bool))) (fun x => oddOn S x = β)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at htot
  omega

end Halving

theorem card_oddOn_fin {k : ℕ} (hk : 1 ≤ k) (β : Bool) :
    #{v : Fin k → Bool | oddOn univ v = β} = 2 ^ (k - 1) := by
  have h := two_mul_card_oddOn_of_mem (S := (univ : Finset (Fin k))) (mem_univ ⟨0, hk⟩) β
  rw [Fintype.card_fin] at h
  have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ]; ring
  omega

theorem toNat_oddOn {ι : Type*} (S : Finset ι) (x : ι → Bool) :
    (oddOn S x).toNat = (∑ t ∈ S, (x t).toNat) % 2 := by
  unfold oddOn
  rcases Nat.even_or_odd (∑ t ∈ S, (x t).toNat) with h | h
  · rw [decide_eq_false (Nat.not_odd_iff_even.mpr h), Nat.even_iff.mp h]; rfl
  · rw [decide_eq_true h, Nat.odd_iff.mp h]; rfl

section Count

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {b : ι → ℕ}

-- The parity outside block `w` is the parity of the other block parities.
theorem stau_eq (X : (Σ w, Fin (b w)) → Bool) (w : ι) :
    stau X w = oddOn (univ.erase w) (sproj X) := by
  have hset : (univ.filter fun p : Σ w, Fin (b w) => p.1 ≠ w)
      = (univ.erase w).sigma (fun _ => univ) := by
    ext ⟨w', j⟩; simp
  unfold stau oddOn
  rw [hset, Finset.sum_sigma]
  rw [decide_eq_decide, Nat.odd_iff, Nat.odd_iff, Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  have : ∀ w' ∈ univ.erase w, (sproj X w').toNat % 2
      = (∑ j, (X ⟨w', j⟩).toNat) % 2 := by
    intro w' _
    show (oddOn univ (sblk X w')).toNat % 2 = _
    rw [toNat_oddOn, Nat.mod_mod]; rfl
  rw [Finset.sum_congr rfl this]

theorem bcol_eq (T : ∀ w, Tmpl (b w)) (C : Col ι) (X : (Σ w, Fin (b w)) → Bool) (w : ι)
    (j : Fin (b w)) :
    (bstep T C).col X ⟨w, j⟩ =
      tcol (T w) (sblk X w) j (C.col (sproj X) w) (oddOn (univ.erase w) (sproj X)) := by
  show bcol T C X ⟨w, j⟩ = _
  unfold bcol
  rw [stau_eq]

-- The fibre lemma: counting `X` by the block parities and by the block at `w`.
theorem card_fibre (hb : ∀ w, 1 ≤ b w) (w : ι)
    (P : (ι → Bool) → (Fin (b w) → Bool) → Prop) [∀ y v, Decidable (P y v)] :
    #{X : (Σ w, Fin (b w)) → Bool | P (sproj X) (sblk X w)} =
      2 ^ (∑ w' ∈ univ.erase w, (b w' - 1)) *
        ∑ y : ι → Bool, #{v : Fin (b w) → Bool | oddOn univ v = y w ∧ P y v} := by
  -- curry: a vertex is a family of blocks
  let ec : ((p : Σ w, Fin (b w)) → Bool) ≃ (∀ w, Fin (b w) → Bool) :=
    Equiv.piCurry (fun (_ : ι) (_ : Fin (b _)) => Bool)
  have h1 : #{X : (Σ w, Fin (b w)) → Bool | P (sproj X) (sblk X w)}
      = #{Y : ∀ w, Fin (b w) → Bool | P (fun w' => oddOn univ (Y w')) (Y w)} := by
    refine Finset.card_equiv ec fun X => ?_
    simp only [mem_filter, mem_univ, true_and]
    rfl
  rw [h1]
  -- split by the block parities
  rw [Finset.card_eq_sum_card_fiberwise (f := fun Y : ∀ w, Fin (b w) → Bool =>
    fun w' => oddOn univ (Y w')) (t := univ) (fun _ _ => mem_univ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  -- on the fibre of `y`, the predicate reads `P y (Y w)`
  have h2 : (filter (fun Y : ∀ w, Fin (b w) → Bool => P (fun w' => oddOn univ (Y w')) (Y w))
      univ).filter (fun Y => (fun w' => oddOn univ (Y w')) = y)
      = univ.filter (fun Y : ∀ w, Fin (b w) → Bool =>
          (oddOn univ (Y w) = y w ∧ P y (Y w)) ∧ ∀ w' : {w' // w' ≠ w}, oddOn univ (Y w') = y w') := by
    ext Y
    simp only [mem_filter, mem_univ, true_and, funext_iff]
    constructor
    · rintro ⟨hP, hy⟩
      refine ⟨⟨hy w, ?_⟩, fun w' => hy w'⟩
      have : (fun w' => oddOn univ (Y w')) = y := funext hy
      rw [this] at hP; exact hP
    · rintro ⟨⟨hw, hP⟩, hrest⟩
      have hy : ∀ w', oddOn univ (Y w') = y w' := fun w' => by
        by_cases h : w' = w
        · subst h; exact hw
        · exact hrest ⟨w', h⟩
      refine ⟨?_, hy⟩
      have : (fun w' => oddOn univ (Y w')) = y := funext hy
      rw [this]; exact hP
  rw [h2]
  -- split off the block at `w`
  have h3 : #(univ.filter (fun Y : ∀ w, Fin (b w) → Bool =>
      (oddOn univ (Y w) = y w ∧ P y (Y w)) ∧ ∀ w' : {w' // w' ≠ w}, oddOn univ (Y w') = y w'))
      = #(univ.filter (fun q : (Fin (b w) → Bool) × (∀ w' : {w' // w' ≠ w}, Fin (b w') → Bool) =>
          (oddOn univ q.1 = y w ∧ P y q.1) ∧ ∀ w', oddOn univ (q.2 w') = y w')) := by
    refine Finset.card_equiv (Equiv.piSplitAt w (fun w' => Fin (b w') → Bool)) fun Y => ?_
    simp only [mem_filter, mem_univ, true_and]
    rfl
  have h5 : univ.filter (fun q : (Fin (b w) → Bool) × (∀ w' : {w' // w' ≠ w}, Fin (b w') → Bool) =>
      (oddOn univ q.1 = y w ∧ P y q.1) ∧ ∀ w', oddOn univ (q.2 w') = y w')
      = (univ.filter fun v : Fin (b w) → Bool => oddOn univ v = y w ∧ P y v) ×ˢ
        (univ.filter fun Z : ∀ w' : {w' // w' ≠ w}, Fin (b w') → Bool =>
          ∀ w', oddOn univ (Z w') = y w') := by
    ext q; simp [Finset.mem_product]
  rw [h3, h5, Finset.card_product, mul_comm]
  congr 1
  -- the other blocks: a product of parity classes
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypePiEquivPi
    (p := fun (w' : {w' // w' ≠ w}) (v : Fin (b w') → Bool) => oddOn univ v = y w')),
    Fintype.card_pi]
  have h4 : ∀ w' : {w' // w' ≠ w},
      Fintype.card {v : Fin (b w') → Bool // oddOn univ v = y w'} = 2 ^ (b w' - 1) := by
    intro w'
    rw [Fintype.card_subtype, card_oddOn_fin (hb w')]
  rw [Finset.prod_congr rfl (fun w' _ => h4 w'), Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Finset.sum_subtype (univ.erase w) (p := fun w' => w' ≠ w) (fun w' => by simp)
    (fun w' => b w' - 1)).symm

-- A parity class of the template, counted by colour.
theorem card_tcol {k : ℕ} (T : Tmpl k) (j : Fin k) (β c π : Bool) :
    #{v : Fin k → Bool | oddOn univ v = β ∧ tcol T v j c π = true}
      = π.toNat * T.e j + (!π).toNat * T.o j + c.toNat * T.a j := by
  rw [← T.cntE j β, ← T.cntO j β, ← T.cntA j β, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hd := T.disj v j
  by_cases hβ : oddOn univ v = β
  · cases hE : T.isE v j <;> cases hO : T.isO v j <;> cases π <;> cases c <;>
      simp_all [tcol]
  · simp [hβ]

-- The number of vertices at which a given direction of the block step is kept.
theorem card_bstep (hb : ∀ w, 1 ≤ b w) (hm : 2 ≤ Fintype.card ι) (T : ∀ w, Tmpl (b w))
    (C : Col ι) (w : ι) (j : Fin (b w)) :
    #{X : (Σ w, Fin (b w)) → Bool | (bstep T C).col X ⟨w, j⟩ = true} =
      2 ^ (∑ w' ∈ univ.erase w, (b w' - 1)) *
        (((T w).e j + (T w).o j) * 2 ^ (Fintype.card ι - 1)
          + (T w).a j * #{y : ι → Bool | C.col y w = true}) := by
  simp only [bcol_eq]
  rw [card_fibre hb w (fun y v =>
    tcol (T w) v j (C.col y w) (oddOn (univ.erase w) y) = true)]
  congr 1
  simp only [card_tcol]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul, ← card_filter_eq_sum_toNat, ← card_filter_eq_sum_toNat,
    ← card_filter_eq_sum_toNat]
  obtain ⟨i, hi⟩ : ∃ i : ι, i ≠ w := Fintype.exists_ne_of_one_lt_card (by omega) w
  have hmem : i ∈ univ.erase w := by simp [hi]
  have ht := two_mul_card_oddOn_of_mem hmem true
  have hf := two_mul_card_oddOn_of_mem hmem false
  have h2 : (2 : ℕ) ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    conv_lhs => rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have e1 : #{y : ι → Bool | oddOn (univ.erase w) y = true} = 2 ^ (Fintype.card ι - 1) := by
    omega
  have e2 : #{y : ι → Bool | (!oddOn (univ.erase w) y) = true} = 2 ^ (Fintype.card ι - 1) := by
    have : #{y : ι → Bool | (!oddOn (univ.erase w) y) = true}
        = #{y : ι → Bool | oddOn (univ.erase w) y = false} := by
      congr 1; ext y; simp
    omega
  rw [e1, e2]
  ring

end Count


/-! ### Transport and double counting -/

section Transport

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ]

-- Transport along a bijection of coordinates preserves the count of each direction.
theorem card_congr_dir (e : ι ≃ κ) (C : Col ι) (k : κ) :
    #{x : κ → Bool | (C.congr e).col x k = true} = #{y : ι → Bool | C.col y (e.symm k) = true} := by
  refine Finset.card_equiv (e.arrowCongr (Equiv.refl Bool)).symm fun x => ?_
  simp only [mem_filter, mem_univ, true_and]
  rfl

-- The degree sum is the sum over directions of the number of vertices keeping that direction.
theorem sum_card_swap (P : (ι → Bool) → ι → Prop) [∀ x i, Decidable (P x i)] :
    ∑ x : ι → Bool, #{i | P x i} = ∑ i : ι, #{x : ι → Bool | P x i} := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

end Transport

/-! ### The tower `Q₄ → Q₁₆ → …`, regular in every direction -/

-- The 24-edge colouring of `Q₄`: the `a`- and `o`-edges of the template.
def base4 : Col (Fin 4) where
  col v j := qcol v j true false
  col_fl v j := qcol_fl v j true false
  noSq v _ _ hjk := qcol_square v hjk true false

theorem card_base4 : ∀ j : Fin 4, #{v : Fin 4 → Bool | qcol v j true false = true} = 12 := by
  decide

-- `Q_{4^r}`, `r ≥ 1`: every direction is kept at `2^(m-1) + 2^(m-1-r)` vertices, `m = 4^r`.
theorem exists_tower (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : Col (Fin (4 ^ r)), ∀ w, 2 ^ (r + 1) * #{y | C.col y w = true} = 2 ^ (4 ^ r) * (2 ^ r + 1) := by
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr'
    · have h4 : 4 = 4 ^ (0 + 1) := by norm_num
      refine ⟨base4.congr (finCongr h4), fun w => ?_⟩
      rw [card_congr_dir]
      have := card_base4 ((finCongr h4).symm w)
      show 2 ^ (0 + 1 + 1) * #{v : Fin 4 → Bool | qcol v _ true false = true} = _
      rw [this]
      norm_num
    · obtain ⟨C, hC⟩ := ih hr'
      have hcard : Fintype.card (Σ _ : Fin (4 ^ r), Fin 4) = 4 ^ (r + 1) := by
        simp [Fintype.card_sigma, pow_succ]
      refine ⟨(bstep (b := fun _ => 4) (fun _ => T4) C).congr (Fintype.equivFinOfCardEq hcard),
        fun w => ?_⟩
      rw [card_congr_dir]
      generalize (Fintype.equivFinOfCardEq hcard).symm w = p
      obtain ⟨w', j⟩ := p
      have hm : 2 ≤ Fintype.card (Fin (4 ^ r)) := by
        rw [Fintype.card_fin]
        have : 4 ≤ 4 ^ r := by
          calc 4 = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) hr'
        omega
      rw [card_bstep (fun _ => by norm_num) hm (fun _ => T4) C w' j]
      have hD := hC w'
      have hsum : ∑ w'' ∈ univ.erase w', ((fun _ => 4) w'' - 1) = 3 * (4 ^ r - 1) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
        ring
      rw [hsum, Fintype.card_fin]
      show 2 ^ (r + 1 + 1) * (2 ^ (3 * (4 ^ r - 1)) * ((2 + 2) * 2 ^ (4 ^ r - 1) + 4 * _))
        = 2 ^ 4 ^ (r + 1) * (2 ^ (r + 1) + 1)
      obtain ⟨m, hm'⟩ : ∃ m, 4 ^ r = m + 1 :=
        ⟨4 ^ r - 1, by have := Nat.one_le_pow r 4 (by norm_num); omega⟩
      have h4m : 4 ^ (r + 1) = 4 * m + 4 := by rw [pow_succ, hm']; ring
      generalize #{y : Fin (4 ^ r) → Bool | C.col y w' = true} = D at hD ⊢
      rw [hm', h4m, Nat.add_sub_cancel]
      rw [hm'] at hD
      have e1 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := by rw [mul_comm, pow_mul]
      have e2 : (2 : ℕ) ^ (4 * m + 4) = 16 * (2 ^ m) ^ 4 := by
        rw [pow_add, mul_comm 4 m, pow_mul]; ring
      have e3 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      have e4 : (2 : ℕ) ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
      have e5 : (2 : ℕ) ^ (r + 1 + 1) = 4 * 2 ^ r := by rw [pow_succ, pow_succ]; ring
      rw [e1, e2, e4, e5]
      rw [e3, e4] at hD
      generalize (2 : ℕ) ^ m = A at hD ⊢
      generalize (2 : ℕ) ^ r = B at hD ⊢
      have : 4 * B * (A ^ 3 * ((2 + 2) * A + 4 * D)) = 16 * B * A ^ 4 + 8 * A ^ 3 * (2 * B * D) := by
        ring
      rw [this, hD]
      ring


/-! ### Mixed block sizes: `t` blocks of size 4, one of size `s`, `u` of size 1 -/

@[simp] theorem T4_e (j : Fin 4) : T4.e j = 2 := rfl
@[simp] theorem T4_o (j : Fin 4) : T4.o j = 2 := rfl
@[simp] theorem T4_a (j : Fin 4) : T4.a j = 4 := rfl
@[simp] theorem T1_e (j : Fin 1) : T1.e j = 0 := rfl
@[simp] theorem T1_o (j : Fin 1) : T1.o j = 0 := rfl
@[simp] theorem T1_a (j : Fin 1) : T1.a j = 1 := rfl

section Mixed

-- Block sizes on the index type `Fin t ⊕ (Unit ⊕ Fin u)`.
def bsz (s t u : ℕ) : Fin t ⊕ (Unit ⊕ Fin u) → ℕ
  | Sum.inl _ => 4
  | Sum.inr (Sum.inl _) => s
  | Sum.inr (Sum.inr _) => 1

-- The templates: `T4` on the first `t` blocks, `Ts` on the middle one, `T1` on the last `u`.
def tsz {s : ℕ} (Ts : Tmpl s) (t u : ℕ) : ∀ w : Fin t ⊕ (Unit ⊕ Fin u), Tmpl (bsz s t u w)
  | Sum.inl _ => T4
  | Sum.inr (Sum.inl _) => Ts
  | Sum.inr (Sum.inr _) => T1

theorem sum_bsz (s t u : ℕ) : ∑ w, (bsz s t u w - 1) = 3 * t + (s - 1) := by
  simp only [Fintype.sum_sum_type, bsz, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_unit, smul_eq_mul]
  omega

theorem sum_erase_bsz {s t u : ℕ} (w : Fin t ⊕ (Unit ⊕ Fin u)) :
    ∑ w' ∈ univ.erase w, (bsz s t u w' - 1) = 3 * t + (s - 1) - (bsz s t u w - 1) := by
  have := Finset.add_sum_erase univ (fun w' => bsz s t u w' - 1) (mem_univ w)
  rw [sum_bsz s t u] at this
  omega

theorem card_sigma_bsz (s t u : ℕ) :
    Fintype.card (Σ w, Fin (bsz s t u w)) = 4 * t + s + u := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp only [Fintype.sum_sum_type, bsz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_unit, smul_eq_mul]
  ring

theorem sum_lin {κ : Type*} [Fintype κ] (c M D : ℕ) (e o a : κ → ℕ) :
    ∑ j, c * ((e j + o j) * M + a j * D) = c * ((∑ j, (e j + o j)) * M + (∑ j, a j) * D) := by
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

-- The degree sum of the mixed step, given a base regular in every direction.
theorem sum_mixed {s t u : ℕ} (Ts : Tmpl s) (hs : 1 ≤ s) (hm : 2 ≤ t + 1 + u)
    (C : Col (Fin t ⊕ (Unit ⊕ Fin u))) (D : ℕ) (hC : ∀ w, #{y | C.col y w = true} = D) :
    ∑ p, #{X | (bstep (tsz Ts t u) C).col X p = true} =
      t * (2 ^ (3 * t + (s - 1) - 3) * (16 * 2 ^ (t + u) + 16 * D))
      + 2 ^ (3 * t) * ((∑ j, (Ts.e j + Ts.o j)) * 2 ^ (t + u) + (∑ j, Ts.a j) * D)
      + u * (2 ^ (3 * t + (s - 1)) * D) := by
  have hb : ∀ w, 1 ≤ bsz s t u w := by
    rintro (_ | _ | _) <;> simp [bsz]
    exact hs
  have hcard : Fintype.card (Fin t ⊕ (Unit ⊕ Fin u)) = t + 1 + u := by simp [add_assoc]
  have hm' : 2 ≤ Fintype.card (Fin t ⊕ (Unit ⊕ Fin u)) := by rw [hcard]; exact hm
  rw [Fintype.sum_sigma]
  simp only [card_bstep hb hm' (tsz Ts t u) C, hC, sum_erase_bsz, hcard, sum_lin]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hE4 : ∀ x : Fin t, ∑ j : Fin (bsz s t u (Sum.inl x)),
      ((tsz Ts t u (Sum.inl x)).e j + (tsz Ts t u (Sum.inl x)).o j) = 16 := fun x => by
    show ∑ j : Fin 4, (T4.e j + T4.o j) = 16
    simp
  have hA4 : ∀ x : Fin t, ∑ j : Fin (bsz s t u (Sum.inl x)),
      (tsz Ts t u (Sum.inl x)).a j = 16 := fun x => by
    show ∑ j : Fin 4, T4.a j = 16
    simp
  have hEs : ∀ x : Unit, ∑ j : Fin (bsz s t u (Sum.inr (Sum.inl x))),
      ((tsz Ts t u (Sum.inr (Sum.inl x))).e j + (tsz Ts t u (Sum.inr (Sum.inl x))).o j)
      = ∑ j, (Ts.e j + Ts.o j) := fun _ => rfl
  have hAs : ∀ x : Unit, ∑ j : Fin (bsz s t u (Sum.inr (Sum.inl x))),
      (tsz Ts t u (Sum.inr (Sum.inl x))).a j = ∑ j, Ts.a j := fun _ => rfl
  have hE1 : ∀ x : Fin u, ∑ j : Fin (bsz s t u (Sum.inr (Sum.inr x))),
      ((tsz Ts t u (Sum.inr (Sum.inr x))).e j + (tsz Ts t u (Sum.inr (Sum.inr x))).o j)
      = 0 := fun x => by
    show ∑ j : Fin 1, (T1.e j + T1.o j) = 0
    simp
  have hA1 : ∀ x : Fin u, ∑ j : Fin (bsz s t u (Sum.inr (Sum.inr x))),
      (tsz Ts t u (Sum.inr (Sum.inr x))).a j = 1 := fun x => by
    show ∑ j : Fin 1, T1.a j = 1
    simp
  simp only [hE4, hA4, hEs, hAs, hE1, hA1]
  simp only [bsz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_unit, smul_eq_mul]
  have h1 : t + 1 + u - 1 = t + u := by omega
  have h2 : 3 * t + (s - 1) - (s - 1) = 3 * t := by omega
  have h3 : 3 * t + (s - 1) - (4 - 1) = 3 * t + (s - 1) - 3 := rfl
  have h4 : 3 * t + (s - 1) - (1 - 1) = 3 * t + (s - 1) := rfl
  rw [h1, h2, h3, h4]
  ring

end Mixed

/-! ### The bound -/

theorem le_f_of_col {n : ℕ} (hn : 1 ≤ n) (C : Col (Fin n)) : #C.graph.edgeFinset ≤ SqueezeBench.HypercubeC4.f n :=
  HypercubeC4.le_f_of_not_hasSquare (by rw [HypercubeC4.nMin_eq]; exact hn) C.graph_le C.not_hasSquare

theorem r_add_three_le (r : ℕ) (hr : 1 ≤ r) : r + 3 ≤ 4 ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr'
    · norm_num
    · have := ih hr'
      rw [pow_succ]; omega

-- The three arithmetic identities, one per size of the middle block.
-- Normalising `mixed n` and the powers of two shared by the three identities.
theorem mixed_eq {r n : ℕ} (hr : 1 ≤ r) (hmn : 4 ^ r ≤ n) (hn4 : n < 4 ^ (r + 1)) :
    mixed n = n * 2 ^ (n - 2) + (4 ^ r + (n - 4 ^ r) / 3) * 2 ^ (n - 2 - r)
      + (if (n - 4 ^ r) % 3 = 2 then 2 ^ (n - 3 - r) else 0) := by
  have hlog : Nat.log 4 n = r := Nat.log_eq_of_pow_le_of_lt_pow hmn hn4
  have h4 : ¬ n < 4 := by have := r_add_three_le r hr; omega
  simp only [mixed, hlog, h4, if_false]

theorem arith1 (r m t u n D : ℕ) (hr : 1 ≤ r) (hm : m = 4 ^ r) (hn : n = 3 * t + m)
    (hu : m = t + 1 + u) (hD : 2 ^ (r + 1) * D = 2 ^ m * (2 ^ r + 1)) :
    t * (2 ^ (3 * t + (1 - 1) - 3) * (16 * 2 ^ (t + u) + 16 * D))
      + 2 ^ (3 * t) * (0 * 2 ^ (t + u) + 1 * D) + u * (2 ^ (3 * t + (1 - 1)) * D)
      = 2 * mixed n := by
  have hr3 := r_add_three_le r hr
  rw [mixed_eq hr (by omega) (by rw [pow_succ]; omega)]
  have hdiv : (n - 4 ^ r) / 3 = t := by omega
  have hmod : (n - 4 ^ r) % 3 = 0 := by omega
  rw [hdiv, hmod, if_neg (by decide), add_zero]
  obtain ⟨q, hq⟩ : ∃ q, n = q + r + 3 := ⟨n - r - 3, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, m = a + r + 1 := ⟨m - r - 1, by omega⟩
  have e1 : n - 2 = q + r + 1 := by omega
  have e2 : n - 2 - r = q + 1 := by omega
  have e3 : t + u = a + r := by omega
  have e4 : 3 * t + (1 - 1) = 3 * t := rfl
  rw [e2, e1, e3, e4, ← hm, hn, hu]
  have hD' : D = 2 ^ r * 2 ^ a + 2 ^ a := by
    have h : 2 ^ (r + 1) * D = 2 ^ (r + 1) * (2 ^ r * 2 ^ a + 2 ^ a) := by
      rw [hD, ha]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hKA : 2 ^ (3 * t) * 2 ^ a = 4 * 2 ^ q := by
    rw [← pow_add, show 3 * t + a = q + 2 by omega, pow_add]; ring
  rw [hD', pow_add 2 a r, pow_succ 2 (q + r), pow_add 2 q r, pow_succ 2 q]
  generalize 2 ^ r = R at hKA ⊢
  generalize 2 ^ a = A at hKA ⊢
  generalize 2 ^ q = P at hKA ⊢
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Nat.mul_zero, pow_zero, one_mul, zero_mul, zero_add] at hKA ⊢
    subst hKA
    ring
  · have hK3 : (2 : ℕ) ^ (3 * t) = 8 * 2 ^ (3 * t - 3) := by
      conv_lhs => rw [show 3 * t = 3 + (3 * t - 3) by omega, pow_add]
      norm_num
    rw [hK3] at hKA ⊢
    generalize 2 ^ (3 * t - 3) = K3 at hKA ⊢
    have hP : P = 2 * K3 * A := by
      have h4 : 4 * P = 4 * (2 * K3 * A) := by rw [← hKA]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
    subst hP
    ring

theorem arith2 (r m t u n D : ℕ) (hr : 1 ≤ r) (hm : m = 4 ^ r) (hn : n = 3 * t + 1 + m)
    (hu : m = t + 1 + u) (hD : 2 ^ (r + 1) * D = 2 ^ m * (2 ^ r + 1)) :
    t * (2 ^ (3 * t + (2 - 1) - 3) * (16 * 2 ^ (t + u) + 16 * D))
      + 2 ^ (3 * t) * (2 * 2 ^ (t + u) + 2 * D) + u * (2 ^ (3 * t + (2 - 1)) * D)
      = 2 * mixed n := by
  have hr3 := r_add_three_le r hr
  rw [mixed_eq hr (by omega) (by rw [pow_succ]; omega)]
  have hdiv : (n - 4 ^ r) / 3 = t := by omega
  have hmod : (n - 4 ^ r) % 3 = 1 := by omega
  rw [hdiv, hmod, if_neg (by decide), add_zero]
  obtain ⟨q, hq⟩ : ∃ q, n = q + r + 3 := ⟨n - r - 3, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, m = a + r + 1 := ⟨m - r - 1, by omega⟩
  have e1 : n - 2 = q + r + 1 := by omega
  have e2 : n - 2 - r = q + 1 := by omega
  have e3 : t + u = a + r := by omega
  have e4 : 3 * t + (2 - 1) = 3 * t + 1 := rfl
  rw [e2, e1, e3, e4, ← hm, hn, hu]
  have hD' : D = 2 ^ r * 2 ^ a + 2 ^ a := by
    have h : 2 ^ (r + 1) * D = 2 ^ (r + 1) * (2 ^ r * 2 ^ a + 2 ^ a) := by
      rw [hD, ha]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hKA : 2 ^ (3 * t) * 2 ^ a = 2 * 2 ^ q := by
    rw [← pow_add, show 3 * t + a = q + 1 by omega, pow_add]; ring
  rw [hD', pow_add 2 a r, pow_succ 2 (q + r), pow_add 2 q r, pow_succ 2 q, pow_succ 2 (3 * t)]
  generalize 2 ^ r = R at hKA ⊢
  generalize 2 ^ a = A at hKA ⊢
  generalize 2 ^ q = P at hKA ⊢
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Nat.mul_zero, pow_zero, one_mul, zero_mul, zero_add] at hKA ⊢
    subst hKA
    ring
  · have hK3 : (2 : ℕ) ^ (3 * t) = 4 * 2 ^ (3 * t - 2) := by
      conv_lhs => rw [show 3 * t = 2 + (3 * t - 2) by omega, pow_add]
      norm_num
    have hK3' : (2 : ℕ) ^ (3 * t + 1 - 3) = 2 ^ (3 * t - 2) := by
      rw [show 3 * t + 1 - 3 = 3 * t - 2 by omega]
    rw [hK3']
    rw [hK3] at hKA ⊢
    generalize 2 ^ (3 * t - 2) = K3 at hKA ⊢
    have hP : P = 2 * K3 * A := by
      have h4 : 2 * P = 2 * (2 * K3 * A) := by rw [← hKA]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
    subst hP
    ring

theorem arith3 (r m t u n D : ℕ) (hr : 1 ≤ r) (hm : m = 4 ^ r) (hn : n = 3 * t + 2 + m)
    (hu : m = t + 1 + u) (hD : 2 ^ (r + 1) * D = 2 ^ m * (2 ^ r + 1)) :
    t * (2 ^ (3 * t + (3 - 1) - 3) * (16 * 2 ^ (t + u) + 16 * D))
      + 2 ^ (3 * t) * (6 * 2 ^ (t + u) + 6 * D) + u * (2 ^ (3 * t + (3 - 1)) * D)
      = 2 * mixed n := by
  have hr3 := r_add_three_le r hr
  rw [mixed_eq hr (by omega) (by rw [pow_succ]; omega)]
  have hdiv : (n - 4 ^ r) / 3 = t := by omega
  have hmod : (n - 4 ^ r) % 3 = 2 := by omega
  rw [hdiv, hmod, if_pos rfl]
  obtain ⟨q, hq⟩ : ∃ q, n = q + r + 3 := ⟨n - r - 3, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, m = a + r + 1 := ⟨m - r - 1, by omega⟩
  have e1 : n - 2 = q + r + 1 := by omega
  have e2 : n - 2 - r = q + 1 := by omega
  have e2' : n - 3 - r = q := by omega
  have e3 : t + u = a + r := by omega
  have e4 : 3 * t + (3 - 1) = 3 * t + 2 := rfl
  rw [e2', e2, e1, e3, e4, ← hm, hn, hu]
  have hD' : D = 2 ^ r * 2 ^ a + 2 ^ a := by
    have h : 2 ^ (r + 1) * D = 2 ^ (r + 1) * (2 ^ r * 2 ^ a + 2 ^ a) := by
      rw [hD, ha]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hKA : 2 ^ (3 * t) * 2 ^ a = 2 ^ q := by
    rw [← pow_add, show 3 * t + a = q by omega]
  rw [hD', pow_add 2 a r, pow_succ 2 (q + r), pow_add 2 q r, pow_succ 2 q,
    pow_add 2 (3 * t) 2]
  generalize 2 ^ r = R at hKA ⊢
  generalize 2 ^ a = A at hKA ⊢
  generalize 2 ^ q = P at hKA ⊢
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Nat.mul_zero, pow_zero, one_mul, zero_mul, zero_add] at hKA ⊢
    subst hKA
    ring
  · have hK3 : (2 : ℕ) ^ (3 * t) = 2 * 2 ^ (3 * t - 1) := by
      conv_lhs => rw [show 3 * t = 1 + (3 * t - 1) by omega, pow_add]
      norm_num
    have hK3' : (2 : ℕ) ^ (3 * t + 2 - 3) = 2 ^ (3 * t - 1) := by
      rw [show 3 * t + 2 - 3 = 3 * t - 1 by omega]
    rw [hK3']
    rw [hK3] at hKA ⊢
    generalize 2 ^ (3 * t - 1) = K3 at hKA ⊢
    subst hKA
    ring

theorem T1_sums : (∑ j : Fin 1, (T1.e j + T1.o j)) = 0 ∧ (∑ j : Fin 1, T1.a j) = 1 := by decide
theorem T2_sums : (∑ j : Fin 2, (T2.e j + T2.o j)) = 2 ∧ (∑ j : Fin 2, T2.a j) = 2 := by decide
theorem T3_sums : (∑ j : Fin 3, (T3.e j + T3.o j)) = 6 ∧ (∑ j : Fin 3, T3.a j) = 6 := by decide

-- The mixed construction, on `Fin n`, with exactly `mixed n` edges.
theorem exists_mixed {n : ℕ} (hn : 4 ≤ n) : ∃ C : Col (Fin n), #C.graph.edgeFinset = mixed n := by
  -- the parameters
  obtain ⟨r, hr⟩ : ∃ r, Nat.log 4 n = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by rw [← hr]; exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hmn : 4 ^ r ≤ n := by rw [← hr]; exact Nat.pow_log_le_self 4 (by omega)
  have hn4 : n < 4 * 4 ^ r := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) n
    rw [hr, pow_succ] at this; omega
  have hm4 : 4 ≤ 4 ^ r := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
  obtain ⟨t, ht⟩ : ∃ t, (n - 4 ^ r) / 3 = t := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, (n - 4 ^ r) % 3 = d := ⟨_, rfl⟩
  have hK : n - 4 ^ r = 3 * t + d := by rw [← ht, ← hd]; exact (Nat.div_add_mod (n - 4 ^ r) 3).symm
  have hd3 : d < 3 := by rw [← hd]; exact Nat.mod_lt _ (by norm_num)
  have htm : t + 1 ≤ 4 ^ r := by omega
  obtain ⟨u, hu⟩ : ∃ u, 4 ^ r = t + 1 + u := ⟨4 ^ r - t - 1, by omega⟩
  -- the base, regular in every direction
  obtain ⟨C₀, hC₀⟩ := exists_tower r hr1
  obtain ⟨D, hD⟩ : ∃ D, 2 ^ (r + 1) * D = 2 ^ (4 ^ r) * (2 ^ r + 1) :=
    ⟨_, hC₀ ⟨0, by omega⟩⟩
  have hC₀' : ∀ w, #{y | C₀.col y w = true} = D := by
    intro w
    have h1 := hC₀ w
    rw [← hD] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hcι : Fintype.card (Fin t ⊕ (Unit ⊕ Fin u)) = 4 ^ r := by simp [hu, add_assoc]
  let eι := Fintype.equivFinOfCardEq hcι
  let C : Col (Fin t ⊕ (Unit ⊕ Fin u)) := C₀.congr eι.symm
  have hC : ∀ w, #{y | C.col y w = true} = D := fun w => by
    show #{y | (C₀.congr eι.symm).col y w = true} = D
    rw [card_congr_dir]; exact hC₀' _
  have hm2 : 2 ≤ t + 1 + u := by omega
  -- the three cases for the middle block
  have key : ∀ (s : ℕ) (Ts : Tmpl s), 1 ≤ s → n = 3 * t + (s - 1) + 4 ^ r →
      ∃ C' : Col (Fin n), 2 * #C'.graph.edgeFinset =
        t * (2 ^ (3 * t + (s - 1) - 3) * (16 * 2 ^ (t + u) + 16 * D))
        + 2 ^ (3 * t) * ((∑ j, (Ts.e j + Ts.o j)) * 2 ^ (t + u) + (∑ j, Ts.a j) * D)
        + u * (2 ^ (3 * t + (s - 1)) * D) := by
    intro s Ts hs hns
    have hcn : Fintype.card (Σ w, Fin (bsz s t u w)) = n := by
      rw [card_sigma_bsz]; omega
    refine ⟨(bstep (tsz Ts t u) C).congr (Fintype.equivFinOfCardEq hcn), ?_⟩
    rw [Col.two_mul_card_edges, Col.sum_card_congr, sum_card_swap, sum_mixed Ts hs hm2 C D hC]
  have hs1 : 1 ≤ d + 1 := by omega
  interval_cases d
  · obtain ⟨C', hC'⟩ := key 1 T1 hs1 (by omega)
    rw [T1_sums.1, T1_sums.2] at hC'
    refine ⟨C', ?_⟩
    have := arith1 r (4 ^ r) t u n D hr1 rfl (by omega) hu hD
    omega
  · obtain ⟨C', hC'⟩ := key 2 T2 hs1 (by omega)
    rw [T2_sums.1, T2_sums.2] at hC'
    refine ⟨C', ?_⟩
    have := arith2 r (4 ^ r) t u n D hr1 rfl (by omega) hu hD
    omega
  · obtain ⟨C', hC'⟩ := key 3 T3 hs1 (by omega)
    rw [T3_sums.1, T3_sums.2] at hC'
    refine ⟨C', ?_⟩
    have := arith3 r (4 ^ r) t u n D hr1 rfl (by omega) hu hD
    omega

theorem mixed_valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f mixed := by
  intro n
  rcases Nat.lt_or_ge n 4 with hn | hn
  · have h : mixed n = 0 := by simp [mixed, hn]
    rw [h]; exact Nat.zero_le _
  · obtain ⟨C, hC⟩ := exists_mixed hn
    rw [← hC]
    exact le_f_of_col (by omega) C

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.HypercubeC4.Lower.V006.valid mixed_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.HypercubeC4.nMin) (n₀ := 7) (by decide)
    (by decide)

end SqueezeBench.HypercubeC4.Lower.V007
