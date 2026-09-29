import SqueezeBench.Problems.HypercubeC4.Records.Lower.V006.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V005.Proof

-- Adapted from Erdos86.lean (JSP-000102, https://github.com/baobingzhang/jsp-000102-erdos86-lean), Apache License 2.0 (LICENSES/Apache-2.0.txt); modified: see REPORT.md.

/-! Record V006 for HypercubeC4, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V006.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V006

open Finset SimpleGraph

/-! ### Flipping a coordinate, over an arbitrary index type -/

-- `x` with coordinate `i` flipped; the cube on any index type `ι` is `ι → Bool`.
def fl {ι : Type*} [DecidableEq ι] (x : ι → Bool) (i : ι) : ι → Bool :=
  fun t => if t = i then !x t else x t

section Fl

variable {ι : Type*} [DecidableEq ι]

@[simp] theorem fl_self (x : ι → Bool) (i : ι) : fl x i i = !x i := by simp [fl]

theorem fl_of_ne (x : ι → Bool) {i t : ι} (h : t ≠ i) : fl x i t = x t := by simp [fl, h]

@[simp] theorem fl_fl (x : ι → Bool) (i : ι) : fl (fl x i) i = x := by
  funext t; by_cases h : t = i <;> simp [fl, h]

theorem fl_comm (x : ι → Bool) (i j : ι) : fl (fl x i) j = fl (fl x j) i := by
  funext t; simp only [fl]; split_ifs <;> simp_all

theorem fl_ne_self (x : ι → Bool) (i : ι) : fl x i ≠ x := fun h => by
  have := congrFun h i; simp at this

theorem fl_injective (x : ι → Bool) : Function.Injective (fl x) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [fl, hij] at this

end Fl

-- On `Fin n`, `fl` is the problem's `flip`.
theorem fl_eq_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : fl x i = HypercubeC4.flip x i := by
  funext t
  rw [HypercubeC4.flip_apply]
  by_cases h : t = i
  · subst h; simp [fl]
  · simp [fl, h]

/-! ### The `Q₄` template: two disjoint perfect matchings `e`, `o`, every square meeting both -/

-- The direction of the `e`-matching edge at the vertex with bits `v 0, v 1, v 2, v 3`.
def eDir : Bool → Bool → Bool → Bool → Fin 4
  | false, false, false, false => 0
  | true, false, false, false => 0
  | false, true, false, false => 2
  | true, true, false, false => 3
  | false, false, true, false => 3
  | true, false, true, false => 1
  | false, true, true, false => 2
  | true, true, true, false => 1
  | false, false, false, true => 1
  | true, false, false, true => 2
  | false, true, false, true => 1
  | true, true, false, true => 3
  | false, false, true, true => 3
  | true, false, true, true => 2
  | false, true, true, true => 0
  | true, true, true, true => 0

-- The direction of the `o`-matching edge at the vertex with bits `v 0, v 1, v 2, v 3`.
def oDir : Bool → Bool → Bool → Bool → Fin 4
  | false, false, false, false => 1
  | true, false, false, false => 3
  | false, true, false, false => 1
  | true, true, false, false => 2
  | false, false, true, false => 0
  | true, false, true, false => 0
  | false, true, true, false => 3
  | true, true, true, false => 2
  | false, false, false, true => 2
  | true, false, false, true => 3
  | false, true, false, true => 0
  | true, true, false, true => 0
  | false, false, true, true => 2
  | true, false, true, true => 1
  | false, true, true, true => 3
  | true, true, true, true => 1

def eD (v : Fin 4 → Bool) : Fin 4 := eDir (v 0) (v 1) (v 2) (v 3)

def oD (v : Fin 4 → Bool) : Fin 4 := oDir (v 0) (v 1) (v 2) (v 3)

-- The colour of the `Q₄`-edge at `v` in direction `j`: `π` on `e`, `!π` on `o`, `c` on the rest.
def qcol (v : Fin 4 → Bool) (j : Fin 4) (c π : Bool) : Bool :=
  if eD v = j then π else if oD v = j then !π else c

theorem forall_fin4_bool {P : (Fin 4 → Bool) → Prop} (h : ∀ a b c d, P ![a, b, c, d]) :
    ∀ v, P v := by
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext j; fin_cases j <;> rfl
  rw [hv]; exact h _ _ _ _

theorem fl_vec (a b c d : Bool) (j : Fin 4) :
    fl ![a, b, c, d] j = ![if j = 0 then !a else a, if j = 1 then !b else b,
      if j = 2 then !c else c, if j = 3 then !d else d] := by
  funext t; fin_cases t <;> fin_cases j <;> rfl

-- `e` is a matching: the edge is an `e`-edge as seen from either end.
theorem eD_fl : ∀ v : Fin 4 → Bool, ∀ j, eD (fl v j) = j ↔ eD v = j := by
  refine forall_fin4_bool ?_
  intro a b c d j
  rw [fl_vec]
  revert a b c d j
  decide

theorem oD_fl : ∀ v : Fin 4 → Bool, ∀ j, oD (fl v j) = j ↔ oD v = j := by
  refine forall_fin4_bool ?_
  intro a b c d j
  rw [fl_vec]
  revert a b c d j
  decide

-- The two matchings are disjoint.
theorem eD_ne_oD : ∀ v : Fin 4 → Bool, eD v ≠ oD v := by
  refine forall_fin4_bool ?_
  decide

-- Every square of `Q₄` contains an `e`-edge.
theorem hasE : ∀ v : Fin 4 → Bool, ∀ j k, j ≠ k →
    eD v = j ∨ eD v = k ∨ eD (fl v k) = j ∨ eD (fl v j) = k := by
  refine forall_fin4_bool ?_
  intro a b c d j k
  rw [fl_vec, fl_vec]
  revert a b c d j k
  decide

-- Every square of `Q₄` contains an `o`-edge.
theorem hasO : ∀ v : Fin 4 → Bool, ∀ j k, j ≠ k →
    oD v = j ∨ oD v = k ∨ oD (fl v k) = j ∨ oD (fl v j) = k := by
  refine forall_fin4_bool ?_
  intro a b c d j k
  rw [fl_vec, fl_vec]
  revert a b c d j k
  decide

-- At every vertex: one `e`-edge, one `o`-edge, two `a`-edges, so `2c + 1` true directions.
theorem card_qcol : ∀ v : Fin 4 → Bool, ∀ c π : Bool,
    #{j | qcol v j c π = true} = 2 * c.toNat + 1 := by
  refine forall_fin4_bool ?_
  decide

theorem qcol_fl (v : Fin 4 → Bool) (j : Fin 4) (c π : Bool) :
    qcol (fl v j) j c π = qcol v j c π := by
  unfold qcol
  by_cases he : eD v = j
  · rw [if_pos ((eD_fl v j).mpr he), if_pos he]
  · rw [if_neg (fun h => he ((eD_fl v j).mp h)), if_neg he]
    by_cases ho : oD v = j
    · rw [if_pos ((oD_fl v j).mpr ho), if_pos ho]
    · rw [if_neg (fun h => ho ((oD_fl v j).mp h)), if_neg ho]

theorem qcol_of_e {v : Fin 4 → Bool} {j : Fin 4} (h : eD v = j) (c π : Bool) :
    qcol v j c π = π := by
  simp [qcol, h]

theorem qcol_of_o {v : Fin 4 → Bool} {j : Fin 4} (h : oD v = j) (c π : Bool) :
    qcol v j c π = !π := by
  have hne : eD v ≠ j := fun he => eD_ne_oD v (he.trans h.symm)
  simp [qcol, hne, h]

theorem qcol_of_a {v : Fin 4 → Bool} {j : Fin 4} (h : ¬ (eD v = j ∨ oD v = j)) (c π : Bool) :
    qcol v j c π = c := by
  rw [not_or] at h
  simp [qcol, h.1, h.2]

-- An `e`- or `o`-edge changes colour when `π` is toggled, whatever happens to `c`.
theorem qcol_ne_of_matched {v : Fin 4 → Bool} {j : Fin 4} (h : eD v = j ∨ oD v = j)
    (c c' π : Bool) : qcol v j c π ≠ qcol v j c' (!π) := by
  rcases h with h | h
  · rw [qcol_of_e h, qcol_of_e h]; cases π <;> simp
  · rw [qcol_of_o h, qcol_of_o h]; cases π <;> simp

-- A square of `Q₄`, all four edges coloured with the same `c, π`, is never all `true`: its
-- `e`-edge has colour `π` and its `o`-edge colour `!π`.
theorem qcol_square (v : Fin 4 → Bool) {j k : Fin 4} (hjk : j ≠ k) (c π : Bool) :
    ¬ (qcol v j c π = true ∧ qcol (fl v k) j c π = true ∧
      qcol v k c π = true ∧ qcol (fl v j) k c π = true) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hπ : π = true := by
    rcases hasE v j k hjk with h | h | h | h
    · rw [qcol_of_e h] at h1; exact h1
    · rw [qcol_of_e h] at h3; exact h3
    · rw [qcol_of_e h] at h2; exact h2
    · rw [qcol_of_e h] at h4; exact h4
  have hπ' : (!π) = true := by
    rcases hasO v j k hjk with h | h | h | h
    · rw [qcol_of_o h] at h1; exact h1
    · rw [qcol_of_o h] at h3; exact h3
    · rw [qcol_of_o h] at h2; exact h2
    · rw [qcol_of_o h] at h4; exact h4
  rw [hπ] at hπ'
  exact Bool.false_ne_true hπ'

/-! ### Parity -/

section Parity

variable {ι : Type*} [DecidableEq ι]

-- Whether `x` has an odd number of `true` coordinates inside `S`.
def oddOn (S : Finset ι) (x : ι → Bool) : Bool := decide (Odd (∑ t ∈ S, (x t).toNat))

theorem oddOn_fl_of_mem {S : Finset ι} (x : ι → Bool) {i : ι} (hi : i ∈ S) :
    oddOn S (fl x i) = !oddOn S x := by
  have h1 := Finset.add_sum_erase S (fun t => (fl x i t).toNat) hi
  have h2 := Finset.add_sum_erase S (fun t => (x t).toNat) hi
  have h3 : ∑ t ∈ S.erase i, (fl x i t).toNat = ∑ t ∈ S.erase i, (x t).toNat :=
    Finset.sum_congr rfl fun t ht => by rw [fl_of_ne x (Finset.ne_of_mem_erase ht)]
  rw [oddOn, oddOn, ← h1, ← h2, h3, fl_self]
  generalize ∑ t ∈ S.erase i, (x t).toNat = N
  rcases Nat.even_or_odd N with h | h <;>
    cases x i <;> simp [add_comm 1 N, h, Nat.not_odd_iff_even.mpr]

theorem oddOn_fl_of_notMem {S : Finset ι} (x : ι → Bool) {i : ι} (hi : i ∉ S) :
    oddOn S (fl x i) = oddOn S x := by
  rw [oddOn, oddOn]
  congr 2
  exact Finset.sum_congr rfl fun t ht => by rw [fl_of_ne x (by rintro rfl; exact hi ht)]

-- Exactly half of all words have odd weight.
theorem two_mul_card_oddOn [Fintype ι] [Nonempty ι] :
    2 * #{x : ι → Bool | oddOn univ x = true} = 2 ^ Fintype.card ι := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hswap :
      #{x : ι → Bool | oddOn univ x = true} = #{x : ι → Bool | ¬ oddOn univ x = true} := by
    refine Finset.card_nbij' (fl · i₀) (fl · i₀) ?_ ?_ ?_ ?_
    · intro x hx; simp_all [oddOn_fl_of_mem x (Finset.mem_univ i₀)]
    · intro x hx; simp_all [oddOn_fl_of_mem x (Finset.mem_univ i₀)]
    · intro x _; simp
    · intro x _; simp
  have htot := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (ι → Bool))) (fun x => oddOn univ x = true)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at htot
  omega

end Parity

/-! ### Colourings whose `true` edges contain no square -/

-- A `2`-colouring of the edges of the cube `ι → Bool`, `col x i` being the colour of the edge
-- from `x` in direction `i`, well defined on edges and with no all-`true` square.
structure Col (ι : Type*) [DecidableEq ι] where
  col : (ι → Bool) → ι → Bool
  col_fl : ∀ x i, col (fl x i) i = col x i
  noSq : ∀ x i j, i ≠ j →
    ¬ (col x i = true ∧ col (fl x j) i = true ∧ col x j = true ∧ col (fl x i) j = true)

/-! ### The substitution step `Q_ι → Q_{ι × Fin 4}` -/

section Step

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- The block of `X` at `w`, a vertex of `Q₄`.
def blk (X : ι × Fin 4 → Bool) (w : ι) : Fin 4 → Bool := fun j => X (w, j)

-- The block parities of `X`, a vertex of `Q_ι`.
def proj (X : ι × Fin 4 → Bool) : ι → Bool := fun w => oddOn univ (blk X w)

-- The parity of `X` outside the block `w`.
def restPar (X : ι × Fin 4 → Bool) (w : ι) : Bool :=
  oddOn (univ.filter fun p : ι × Fin 4 => p.1 ≠ w) X

omit [Fintype ι] in
theorem blk_fl_self (X : ι × Fin 4 → Bool) (w : ι) (j : Fin 4) :
    blk (fl X (w, j)) w = fl (blk X w) j := by
  funext k; by_cases h : k = j <;> simp [blk, fl, h]

omit [Fintype ι] in
theorem blk_fl_of_ne (X : ι × Fin 4 → Bool) {w w' : ι} (h : w' ≠ w) (j : Fin 4) :
    blk (fl X (w', j)) w = blk X w := by
  funext k; simp [blk, fl, Ne.symm h]

omit [Fintype ι] in
theorem proj_fl (X : ι × Fin 4 → Bool) (w : ι) (j : Fin 4) :
    proj (fl X (w, j)) = fl (proj X) w := by
  funext w'
  by_cases h : w' = w
  · subst h
    rw [fl_self, proj, proj, blk_fl_self, oddOn_fl_of_mem _ (mem_univ _)]
  · rw [fl_of_ne _ h, proj, proj, blk_fl_of_ne X (Ne.symm h)]

theorem restPar_fl_self (X : ι × Fin 4 → Bool) (w : ι) (j : Fin 4) :
    restPar (fl X (w, j)) w = restPar X w :=
  oddOn_fl_of_notMem X (by simp)

theorem restPar_fl_of_ne (X : ι × Fin 4 → Bool) {w w' : ι} (h : w' ≠ w) (j : Fin 4) :
    restPar (fl X (w', j)) w = !restPar X w :=
  oddOn_fl_of_mem X (by simpa using h)

-- The Brass–Harborth–Nienborg substitution step. Inside the block `w`, the `e`-edges of `Q₄` get
-- the parity of `X` outside the block, the `o`-edges the opposite parity, and the `a`-edges copy
-- the colour of the `w`-edge of `Q_ι` at the vector of block parities.
def Col.step (C : Col ι) : Col (ι × Fin 4) where
  col X p := qcol (blk X p.1) p.2 (C.col (proj X) p.1) (restPar X p.1)
  col_fl X p := by
    obtain ⟨w, j⟩ := p
    simp only
    rw [blk_fl_self, proj_fl, C.col_fl, restPar_fl_self, qcol_fl]
  noSq X p q hpq := by
    obtain ⟨w, j⟩ := p
    obtain ⟨w', k⟩ := q
    simp only
    by_cases hw : w = w'
    · subst hw
      have hjk : j ≠ k := fun h => hpq (by rw [h])
      rw [blk_fl_self, blk_fl_self, proj_fl, proj_fl, C.col_fl,
        restPar_fl_self, restPar_fl_self]
      exact qcol_square _ hjk _ _
    · rw [blk_fl_of_ne X (Ne.symm hw), blk_fl_of_ne X hw, proj_fl, proj_fl,
        restPar_fl_of_ne X (Ne.symm hw), restPar_fl_of_ne X hw]
      rintro ⟨h1, h2, h3, h4⟩
      by_cases hA : eD (blk X w) = j ∨ oD (blk X w) = j
      · exact qcol_ne_of_matched hA _ _ _ (h1.trans h2.symm)
      by_cases hB : eD (blk X w') = k ∨ oD (blk X w') = k
      · exact qcol_ne_of_matched hB _ _ _ (h3.trans h4.symm)
      rw [qcol_of_a hA] at h1 h2
      rw [qcol_of_a hB] at h3 h4
      exact C.noSq (proj X) w w' hw ⟨h1, h2, h3, h4⟩

omit [DecidableEq ι] in
theorem card_filter_prod (P : ι × Fin 4 → Prop) [DecidablePred P] :
    #{p | P p} = ∑ w, #{j | P (w, j)} := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _

theorem card_filter_eq_sum_toNat {κ : Type*} [Fintype κ] (b : κ → Bool) :
    #{w | b w = true} = ∑ w, (b w).toNat := by
  rw [card_filter]
  exact Finset.sum_congr rfl fun w _ => by cases b w <;> rfl

-- The number of `true` directions at `X` after the step: two per `true` direction of `Q_ι` at
-- the block parities, plus one per block.
theorem Col.card_step (C : Col ι) (X : ι × Fin 4 → Bool) :
    #{p | C.step.col X p = true} = 2 * #{w | C.col (proj X) w = true} + Fintype.card ι := by
  have hc : Fintype.card ι = ∑ _w : ι, 1 := by simp
  rw [card_filter_prod, card_filter_eq_sum_toNat, Finset.mul_sum, hc, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => card_qcol _ _ _

end Step

/-! ### Transport along a bijection of coordinates, and adding one coordinate -/

section Transfer

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem fl_comp_equiv (e : ι ≃ κ) (x : κ → Bool) (k : κ) :
    fl x k ∘ e = fl (x ∘ e) (e.symm k) := by
  funext i
  simp only [Function.comp, fl, ← Equiv.eq_symm_apply]

def Col.congr (e : ι ≃ κ) (C : Col ι) : Col κ where
  col x k := C.col (x ∘ e) (e.symm k)
  col_fl x k := by
    rw [fl_comp_equiv, C.col_fl]
  noSq x k l hkl := by
    rw [fl_comp_equiv, fl_comp_equiv]
    exact C.noSq (x ∘ e) (e.symm k) (e.symm l) (fun h => hkl (e.symm.injective h))

theorem Col.card_congr [Fintype ι] [Fintype κ] (e : ι ≃ κ) (C : Col ι) (x : κ → Bool) :
    #{k | (C.congr e).col x k = true} = #{i | C.col (x ∘ e) i = true} := by
  refine (Finset.card_equiv e.symm fun k => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem Col.sum_card_congr [Fintype ι] [Fintype κ] (e : ι ≃ κ) (C : Col ι) :
    ∑ x, #{k | (C.congr e).col x k = true} = ∑ y, #{i | C.col y i = true} := by
  simp only [Col.card_congr]
  exact Fintype.sum_equiv (e.symm.arrowCongr (Equiv.refl Bool)) _ _ fun x => rfl

-- Add one coordinate, coloured by the parity of the old coordinates.
def Col.extend [Fintype ι] (C : Col ι) : Col (Option ι) where
  col x o := match o with
    | none => oddOn univ (fun t => x (some t))
    | some i => C.col (fun t => x (some t)) i
  col_fl x o := by
    cases o with
    | none => simp only [fl_of_ne x (Option.some_ne_none _)]
    | some i =>
      simp only
      have : (fun t => fl x (some i) (some t)) = fl (fun t => x (some t)) i := by
        funext t; simp [fl]
      rw [this, C.col_fl]
  noSq x o₁ o₂ h := by
    have hsome :
        ∀ i, (fun t => fl x (some i) (some t)) = fl (fun t => x (some t)) i := by
      intro i; funext t; simp [fl]
    cases o₁ with
    | none =>
      cases o₂ with
      | none => exact absurd rfl h
      | some j =>
        rintro ⟨h1, h2, -, -⟩
        simp only [hsome, oddOn_fl_of_mem _ (mem_univ j)] at h1 h2
        rw [h1] at h2
        exact Bool.false_ne_true h2
    | some i =>
      cases o₂ with
      | none =>
        rintro ⟨-, -, h3, h4⟩
        simp only [hsome, oddOn_fl_of_mem _ (mem_univ i)] at h3 h4
        rw [h3] at h4
        exact Bool.false_ne_true h4
      | some j =>
        simp only [hsome]
        exact C.noSq _ i j (fun hij => h (by rw [hij]))

theorem Col.card_extend [Fintype ι] (C : Col ι) (x : Option ι → Bool) :
    #{o | C.extend.col x o = true} =
      (oddOn univ (fun t => x (some t))).toNat + #{i | C.col (fun t => x (some t)) i = true} := by
  rw [card_filter, Fintype.sum_option, card_filter]
  congr 1
  show (if oddOn univ (fun t => x (some t)) = true then 1 else 0) = _
  cases oddOn univ (fun t => x (some t)) <;> rfl

theorem Col.sum_card_extend [Fintype ι] [Nonempty ι] (C : Col ι) :
    ∑ x, #{o | C.extend.col x o = true} =
      2 * ∑ y, #{i | C.col y i = true} + 2 ^ Fintype.card ι := by
  simp only [Col.card_extend]
  have h := Fintype.sum_equiv (Equiv.piOptionEquivProd (β := fun _ => Bool))
    (fun x : Option ι → Bool =>
      (oddOn univ (fun t => x (some t))).toNat + #{i | C.col (fun t => x (some t)) i = true})
    (fun p : Bool × (ι → Bool) => (oddOn univ p.2).toNat + #{i | C.col p.2 i = true})
    fun x => rfl
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [← card_filter_eq_sum_toNat, ← two_mul_card_oddOn]
  ring

end Transfer

/-! ### The iterated construction -/

-- The Brass–Harborth–Nienborg colouring of `Q_{4^r}`: every vertex has exactly `(4^r + 2^r)/2`
-- `true` directions.
theorem exists_col_four_pow (r : ℕ) :
    ∃ C : Col (Fin (4 ^ r)), ∀ x, 2 * #{i | C.col x i = true} = 4 ^ r + 2 ^ r := by
  induction r with
  | zero =>
    refine ⟨⟨fun _ _ => true, fun _ _ => rfl, fun x i j hij => ?_⟩, fun x => ?_⟩
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; simp only [pow_zero] at *; omega))
        hij
    · simp
  | succ r ih =>
    obtain ⟨C, hC⟩ := ih
    let e : Fin (4 ^ r) × Fin 4 ≃ Fin (4 ^ (r + 1)) :=
      finProdFinEquiv.trans (finCongr (pow_succ 4 r).symm)
    refine ⟨C.step.congr e, fun x => ?_⟩
    rw [Col.card_congr, Col.card_step, Fintype.card_fin]
    have := hC (proj (x ∘ e))
    have h4 : 4 ^ (r + 1) = 4 ^ r * 4 := pow_succ 4 r
    have h2 : 2 ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
    omega

-- Adding `t` further coordinates to the colouring of `Q_{4^r}`.
theorem exists_col_add (r t : ℕ) :
    ∃ C : Col (Fin (4 ^ r + t)),
      2 * ∑ x, #{i | C.col x i = true} = 2 ^ (4 ^ r + t) * (4 ^ r + t + 2 ^ r) := by
  induction t with
  | zero =>
    obtain ⟨C, hC⟩ := exists_col_four_pow r
    refine ⟨C, ?_⟩
    show 2 * ∑ x : Fin (4 ^ r) → Bool, #{i | C.col x i = true} = 2 ^ (4 ^ r) * (4 ^ r + 2 ^ r)
    rw [Finset.mul_sum]
    simp only [hC, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, smul_eq_mul]
  | succ t ih =>
    obtain ⟨C, hC⟩ := ih
    have : Nonempty (Fin (4 ^ r + t)) := ⟨⟨0, by positivity⟩⟩
    refine ⟨C.extend.congr (finSuccEquiv (4 ^ r + t)).symm, ?_⟩
    rw [Col.sum_card_congr, Col.sum_card_extend, Fintype.card_fin]
    calc 2 * (2 * ∑ y, #{i | C.col y i = true} + 2 ^ (4 ^ r + t))
        = 2 * (2 * ∑ y, #{i | C.col y i = true}) + 2 * 2 ^ (4 ^ r + t) := by ring
      _ = 2 ^ (4 ^ r + (t + 1)) * (4 ^ r + (t + 1) + 2 ^ r) := by rw [hC]; ring

/-! ### The subgraph of the cube, its squares and its edges -/

section Graph

variable {n : ℕ} (C : Col (Fin n))

-- The subgraph of `Qₙ` formed by the `true` edges.
def Col.graph : SimpleGraph (Fin n → Bool) where
  Adj x y := ∃ i, y = HypercubeC4.flip x i ∧ C.col x i = true
  symm := ⟨fun x y ⟨i, hy, h⟩ => ⟨i, by rw [hy, HypercubeC4.flip_flip],
    by rw [hy, ← fl_eq_flip, C.col_fl]; exact h⟩⟩
  loopless := ⟨fun x ⟨i, h, _⟩ => by
    have := congrFun h i
    rw [HypercubeC4.flip_apply, if_pos rfl] at this
    cases x i <;> simp at this⟩

instance Col.decGraph : DecidableRel C.graph.Adj := fun x y =>
  inferInstanceAs (Decidable (∃ i, y = HypercubeC4.flip x i ∧ C.col x i = true))

theorem Col.graph_le : C.graph ≤ HypercubeC4.hypercube n := fun _ _ ⟨i, hy, _⟩ =>
  HypercubeC4.hypercube_adj_iff.mpr ⟨i, hy⟩

theorem Col.graph_adj_flip (x : Fin n → Bool) (i : Fin n) :
    C.graph.Adj x (HypercubeC4.flip x i) ↔ C.col x i = true := by
  constructor
  · rintro ⟨j, hj, h⟩
    have hij : i = j := V001.flip_inj x hj
    subst hij
    exact h
  · intro h
    exact ⟨i, rfl, h⟩

-- No square survives: the four edges of a square of `Qₙ` are the four colours `noSq` forbids.
theorem Col.not_hasSquare : ¬ HypercubeC4.HasSquare C.graph := by
  rintro ⟨x, i, j, hij, h1, h2, h3, h4⟩
  rw [Col.graph_adj_flip] at h1 h2 h3
  rw [V005.flip_comm x hij, Col.graph_adj_flip] at h4
  rw [← fl_eq_flip] at h3 h4
  exact C.noSq x i j hij ⟨h1, h4, h2, h3⟩

theorem Col.degree_graph (x : Fin n → Bool) :
    C.graph.degree x = #{i | C.col x i = true} := by
  rw [← card_neighborFinset_eq_degree]
  have : C.graph.neighborFinset x =
      (univ.filter fun i => C.col x i = true).image (HypercubeC4.flip x) := by
    ext y
    simp only [mem_neighborFinset, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl, h⟩; exact ⟨i, h, rfl⟩
    · rintro ⟨i, h, rfl⟩; exact ⟨i, rfl, h⟩
  rw [this, card_image_of_injective _ (fun i j h => V001.flip_inj x h)]

theorem Col.two_mul_card_edges :
    2 * #C.graph.edgeFinset = ∑ x, #{i | C.col x i = true} := by
  rw [← sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl fun x _ => C.degree_graph x

end Graph

/-! ### The bound -/

-- For `n ≥ 1`, with `L = ⌊log₄ n⌋`: a square-free subgraph with `2ⁿ (n + 2^L) / 4` edges.
theorem bhn_le {n : ℕ} (hn : 1 ≤ n) : bhn n ≤ SqueezeBench.HypercubeC4.f n := by
  obtain ⟨L, hL⟩ : ∃ L, Nat.log 4 n = L := ⟨_, rfl⟩
  have hle : 4 ^ L ≤ n := by rw [← hL]; exact Nat.pow_log_le_self 4 (by omega)
  obtain ⟨t, ht⟩ : ∃ t, n = 4 ^ L + t := ⟨n - 4 ^ L, by omega⟩
  subst ht
  obtain ⟨C, hC⟩ := exists_col_add L t
  have h2 := C.two_mul_card_edges
  have key : 4 * #C.graph.edgeFinset = 2 ^ (4 ^ L + t) * (4 ^ L + t + 2 ^ L) := by
    rw [← hC, ← h2]; ring
  have hbhn : bhn (4 ^ L + t) = #C.graph.edgeFinset := by
    show 2 ^ (4 ^ L + t) * (4 ^ L + t + 2 ^ Nat.log 4 (4 ^ L + t)) / 4 = _
    rw [hL, ← key]
    omega
  rw [hbhn]
  exact HypercubeC4.le_f_of_not_hasSquare (by rw [HypercubeC4.nMin_eq]; exact hn)
    C.graph_le C.not_hasSquare

theorem bhn_valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f bhn := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : bhn 0 = 0 := by decide
    rw [h]
    exact Nat.zero_le _
  · exact bhn_le hn

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.HypercubeC4.Lower.V005.valid bhn_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V005.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V005.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.HypercubeC4.nMin) (n₀ := 16) (by decide)
    (by decide)

end SqueezeBench.HypercubeC4.Lower.V006
