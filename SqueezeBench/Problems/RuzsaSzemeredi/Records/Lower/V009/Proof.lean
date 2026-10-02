import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V009.Def
import SqueezeBench.Problems.RuzsaSzemeredi.Records.Lower.V008.Proof

/-! Record V009 for RuzsaSzemeredi, lower direction, by Pablo Manrique

**Tensor products and disjoint unions** (`Ops`). A graph is locally linear iff every edge has
exactly one common neighbour (`common_of_ll`, `ll_of_common`). In the tensor product the common
neighbours of `(x, y)` and `(x', y')` are the pairs of common neighbours, so the product of two
locally linear graphs is locally linear; its degrees multiply, so it has `2 · e(G) · e(H)` edges,
and with Mathlib's `LocallyLinear.card_edgeFinset` (`e = 3 · t`) it has `6 · t(G) · t(H)`
triangles. The disjoint union is handled the same way, with `e(G) + e(H)` edges. Applied to
extremal graphs from `ruzsaSzemerediNumber_spec`, this gives `six_mul_le` and `add_le`.

**Two small graphs** (`Mask`). A graph on `Fin n` is given by one `n²`-bit mask; the kernel checks
the data once (`MaskOk`: irreflexive, symmetric, and for every edge the common neighbours are
exactly one predicted vertex, `n³` bit lookups) and the degrees; `ll_gM` and `card_gM` turn that
into local linearity and the triangle count `n · d / 6`. -/

namespace SqueezeBench.RuzsaSzemeredi.Lower.V009

open SqueezeBench Finset SimpleGraph

/-! ### Locally linear graphs, tensor products and disjoint unions -/

namespace Ops

variable {α : Type*} {G : SimpleGraph α}

/-- The edge `xy` and a common neighbour `z` form a triangle. -/
theorem tri_of_common [DecidableEq α] {x y z : α} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : G.Adj y z) : G.IsNClique 3 ({x, y, z} : Finset α) := by
  rw [is3Clique_iff]; exact ⟨x, y, z, hxy, hxz, hyz, rfl⟩

/-- In a locally linear graph every edge has exactly one common neighbour. -/
theorem common_of_ll (hG : G.LocallyLinear) {x y : α} (hxy : G.Adj x y) :
    ∃ z, G.Adj x z ∧ G.Adj y z ∧ ∀ w, G.Adj x w → G.Adj y w → w = z := by
  classical
  obtain ⟨s, hs, hx, hy⟩ := hG.2 hxy
  have hz : ∃ z, G.Adj x z ∧ G.Adj y z := by
    rw [is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact absurd hxy (G.irrefl)
      | exact ⟨_, hac, hbc⟩ | exact ⟨_, hab, hbc.symm⟩ | exact ⟨_, hbc, hac⟩
      | exact ⟨_, hab.symm, hac.symm⟩ | exact ⟨_, hbc.symm, hab⟩ | exact ⟨_, hac.symm, hab.symm⟩
  obtain ⟨z, hxz, hyz⟩ := hz
  refine ⟨z, hxz, hyz, fun w hxw hyw => ?_⟩
  by_contra hwz
  have h1 := tri_of_common hxy hxz hyz
  have h2 := tri_of_common hxy hxw hyw
  have hne : ({x, y, z} : Finset α) ≠ {x, y, w} := by
    intro h
    have : w ∈ ({x, y, z} : Finset α) := by rw [h]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact G.irrefl hxw
    · exact G.irrefl hyw
    · exact hwz rfl
  have := hG.1 (mem_cliqueSet_iff.2 h1) (mem_cliqueSet_iff.2 h2) hne
  exact hxy.ne (this (by simp) (by simp))

/-- A graph in which every edge has exactly one common neighbour is locally linear. -/
theorem ll_of_common
    (h : ∀ x y, G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z ∧ ∀ w, G.Adj x w → G.Adj y w → w = z) :
    G.LocallyLinear := by
  classical
  refine ⟨?_, fun x y hxy => ?_⟩
  · intro s hs t ht hst
    rw [mem_cliqueSet_iff] at hs ht
    by_contra hcon
    rw [Set.not_subsingleton_iff] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := hcon
    simp only [Set.mem_inter_iff, mem_coe] at hx hy
    have hadj : G.Adj x y := hs.isClique hx.1 hy.1 hxy
    obtain ⟨z, hxz, hyz, hu⟩ := h x y hadj
    have key : ∀ u : Finset α, G.IsNClique 3 u → x ∈ u → y ∈ u → u = {x, y, z} := by
      intro u hu' hxu hyu
      refine eq_of_subset_of_card_le (fun w hw => ?_) ?_
      · simp only [mem_insert, mem_singleton]
        by_cases hwx : w = x
        · exact Or.inl hwx
        by_cases hwy : w = y
        · exact Or.inr (Or.inl hwy)
        exact Or.inr (Or.inr (hu w (hu'.isClique hxu hw (Ne.symm hwx))
          (hu'.isClique hyu hw (Ne.symm hwy))))
      · rw [hu'.card_eq]; exact card_le_three
    exact hst ((key s hs hx.1 hy.1).trans (key t ht hx.2 hy.2).symm)
  · obtain ⟨z, hxz, hyz, -⟩ := h x y hxy
    exact ⟨{x, y, z}, tri_of_common hxy hxz hyz, by simp, by simp⟩

/-- The tensor (categorical) product of two graphs. -/
def tensor {β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj p q := G.Adj p.1 q.1 ∧ H.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem tensor_adj {β : Type*} {H : SimpleGraph β} {p q : α × β} :
    (tensor G H).Adj p q ↔ G.Adj p.1 q.1 ∧ H.Adj p.2 q.2 := Iff.rfl

instance {β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj]
    [DecidableRel H.Adj] : DecidableRel (tensor G H).Adj :=
  fun p q => inferInstanceAs (Decidable (G.Adj p.1 q.1 ∧ H.Adj p.2 q.2))

theorem tensor_ll {β : Type*} {H : SimpleGraph β} (hG : G.LocallyLinear) (hH : H.LocallyLinear) :
    (tensor G H).LocallyLinear := by
  refine ll_of_common fun p q hpq => ?_
  rw [tensor_adj] at hpq
  obtain ⟨z₁, h1, h2, hu1⟩ := common_of_ll hG hpq.1
  obtain ⟨z₂, h3, h4, hu2⟩ := common_of_ll hH hpq.2
  refine ⟨(z₁, z₂), ⟨h1, h3⟩, ⟨h2, h4⟩, fun w hw1 hw2 => ?_⟩
  rw [tensor_adj] at hw1 hw2
  exact Prod.ext (hu1 _ hw1.1 hw2.1) (hu2 _ hw1.2 hw2.2)

theorem tensor_card_edges {β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj] :
    #(tensor G H).edgeFinset = 2 * (#G.edgeFinset * #H.edgeFinset) := by
  have hdeg : ∀ p : α × β, (tensor G H).degree p = G.degree p.1 * H.degree p.2 := by
    intro p
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      ← card_neighborFinset_eq_degree, ← card_product]
    congr 1
    ext q
    simp [tensor_adj]
  have hs := sum_degrees_eq_twice_card_edges (tensor G H)
  have hG := sum_degrees_eq_twice_card_edges G
  have hH := sum_degrees_eq_twice_card_edges H
  simp only [hdeg, Fintype.sum_prod_type] at hs
  have hm : (∑ x, G.degree x) * (∑ y, H.degree y) = ∑ x, ∑ y, G.degree x * H.degree y :=
    Finset.sum_mul_sum _ _ _ _
  rw [← hm, hG, hH] at hs
  have e : 2 * #(tensor G H).edgeFinset = 2 * (2 * (#G.edgeFinset * #H.edgeFinset)) := by
    rw [← hs]; ring
  omega

theorem tensor_card_tri {β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.LocallyLinear) (hH : H.LocallyLinear) :
    #((tensor G H).cliqueFinset 3) = 6 * (#(G.cliqueFinset 3) * #(H.cliqueFinset 3)) := by
  have e := tensor_card_edges (G := G) (H := H)
  rw [(tensor_ll hG hH).card_edgeFinset, hG.card_edgeFinset, hH.card_edgeFinset] at e
  linarith

/-- The disjoint union of two graphs. -/
def dsum {β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj p q := Sum.elim (fun a => Sum.elim (G.Adj a) (fun _ => False) q)
    (fun a => Sum.elim (fun _ => False) (H.Adj a) q) p
  symm := ⟨fun p q h => by
    cases p <;> cases q <;> simp only [Sum.elim_inl, Sum.elim_inr] at h ⊢ <;> exact h.symm⟩
  loopless := ⟨fun p h => by
    cases p <;> simp only [Sum.elim_inl, Sum.elim_inr] at h <;> exact SimpleGraph.irrefl _ h⟩

section dsum
variable {β : Type*} {H : SimpleGraph β}

@[simp] theorem dsum_ll' {a b : α} : (dsum G H).Adj (.inl a) (.inl b) ↔ G.Adj a b := Iff.rfl
@[simp] theorem dsum_rr {a b : β} : (dsum G H).Adj (.inr a) (.inr b) ↔ H.Adj a b := Iff.rfl
@[simp] theorem dsum_lr {a : α} {b : β} : ¬(dsum G H).Adj (.inl a) (.inr b) := fun h => h
@[simp] theorem dsum_rl {a : β} {b : α} : ¬(dsum G H).Adj (.inr a) (.inl b) := fun h => h

instance [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (dsum G H).Adj
  | .inl _, .inl _ => decidable_of_iff _ dsum_ll'.symm
  | .inr _, .inr _ => decidable_of_iff _ dsum_rr.symm
  | .inl _, .inr _ => isFalse dsum_lr
  | .inr _, .inl _ => isFalse dsum_rl

theorem dsum_ll (hG : G.LocallyLinear) (hH : H.LocallyLinear) : (dsum G H).LocallyLinear := by
  refine ll_of_common fun p q hpq => ?_
  rcases p with a | a <;> rcases q with b | b
  · rw [dsum_ll'] at hpq
    obtain ⟨z, h1, h2, hu⟩ := common_of_ll hG hpq
    refine ⟨.inl z, h1, h2, fun w hw1 hw2 => ?_⟩
    rcases w with w | w
    · exact congrArg _ (hu w hw1 hw2)
    · exact absurd hw1 dsum_lr
  · exact absurd hpq dsum_lr
  · exact absurd hpq dsum_rl
  · rw [dsum_rr] at hpq
    obtain ⟨z, h1, h2, hu⟩ := common_of_ll hH hpq
    refine ⟨.inr z, h1, h2, fun w hw1 hw2 => ?_⟩
    rcases w with w | w
    · exact absurd hw1 dsum_rl
    · exact congrArg _ (hu w hw1 hw2)

theorem dsum_card_edges [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    #(dsum G H).edgeFinset = #G.edgeFinset + #H.edgeFinset := by
  have hl : ∀ a : α, (dsum G H).degree (.inl a) = G.degree a := by
    intro a
    have e : (dsum G H).neighborFinset (.inl a) =
        (G.neighborFinset a).map Function.Embedding.inl := by
      ext q
      rcases q with b | b <;> simp
    rw [← card_neighborFinset_eq_degree, e, card_map, card_neighborFinset_eq_degree]
  have hr : ∀ a : β, (dsum G H).degree (.inr a) = H.degree a := by
    intro a
    have e : (dsum G H).neighborFinset (.inr a) =
        (H.neighborFinset a).map Function.Embedding.inr := by
      ext q
      rcases q with b | b <;> simp
    rw [← card_neighborFinset_eq_degree, e, card_map, card_neighborFinset_eq_degree]
  have hs := sum_degrees_eq_twice_card_edges (dsum G H)
  rw [Fintype.sum_sum_type] at hs
  simp only [hl, hr, sum_degrees_eq_twice_card_edges] at hs
  omega

theorem dsum_card_tri [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hG : G.LocallyLinear) (hH : H.LocallyLinear) :
    #((dsum G H).cliqueFinset 3) = #(G.cliqueFinset 3) + #(H.cliqueFinset 3) := by
  have e := dsum_card_edges (G := G) (H := H)
  rw [(dsum_ll hG hH).card_edgeFinset, hG.card_edgeFinset, hH.card_edgeFinset] at e
  omega

end dsum

end Ops

open Ops

/-- Monotonicity of `f` with no lower limit on the smaller argument. -/
theorem f_le_of_le {m n : ℕ} (h : m ≤ n) :
    SqueezeBench.RuzsaSzemeredi.f m ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · simp [SqueezeBench.RuzsaSzemeredi.f, SqueezeBench.RuzsaSzemeredi.nMin, hm]
  · exact SqueezeBench.RuzsaSzemeredi.f_mono hm h

/-- The tensor product bound: `6 · f a · f b ≤ f (a · b)`. -/
theorem six_mul_le (a b : ℕ) :
    6 * SqueezeBench.RuzsaSzemeredi.f a * SqueezeBench.RuzsaSzemeredi.f b ≤
      SqueezeBench.RuzsaSzemeredi.f (a * b) := by
  rcases Nat.lt_or_ge a 3 with ha | ha
  · simp [SqueezeBench.RuzsaSzemeredi.f, SqueezeBench.RuzsaSzemeredi.nMin, ha]
  rcases Nat.lt_or_ge b 3 with hb | hb
  · simp [SqueezeBench.RuzsaSzemeredi.f, SqueezeBench.RuzsaSzemeredi.nMin, hb]
  have hab : 3 ≤ a * b := le_trans ha (Nat.le_mul_of_pos_right a (by omega))
  rw [SqueezeBench.RuzsaSzemeredi.f_of_le ha, SqueezeBench.RuzsaSzemeredi.f_of_le hb,
    SqueezeBench.RuzsaSzemeredi.f_of_le hab]
  obtain ⟨G, iG, hGc, hG⟩ := ruzsaSzemerediNumber_spec (α := Fin a)
  obtain ⟨H, iH, hHc, hH⟩ := ruzsaSzemerediNumber_spec (α := Fin b)
  have h := (tensor_ll hG hH).le_ruzsaSzemerediNumber
  have e : ruzsaSzemerediNumber (Fin a × Fin b) = ruzsaSzemerediNumberNat (a * b) := by
    rw [← ruzsaSzemerediNumberNat_card]; simp
  rw [tensor_card_tri hG hH, hGc, hHc, e] at h
  unfold ruzsaSzemerediNumberNat
  rw [mul_assoc]; exact h

/-- Disjoint unions: `f a + f b ≤ f (a + b)`. -/
theorem add_le (a b : ℕ) :
    SqueezeBench.RuzsaSzemeredi.f a + SqueezeBench.RuzsaSzemeredi.f b ≤
      SqueezeBench.RuzsaSzemeredi.f (a + b) := by
  rcases Nat.lt_or_ge a 3 with ha | ha
  · rw [show SqueezeBench.RuzsaSzemeredi.f a = 0 by
      simp [SqueezeBench.RuzsaSzemeredi.f, SqueezeBench.RuzsaSzemeredi.nMin, ha], zero_add]
    exact f_le_of_le (by omega)
  rcases Nat.lt_or_ge b 3 with hb | hb
  · rw [show SqueezeBench.RuzsaSzemeredi.f b = 0 by
      simp [SqueezeBench.RuzsaSzemeredi.f, SqueezeBench.RuzsaSzemeredi.nMin, hb], add_zero]
    exact f_le_of_le (by omega)
  rw [SqueezeBench.RuzsaSzemeredi.f_of_le ha, SqueezeBench.RuzsaSzemeredi.f_of_le hb,
    SqueezeBench.RuzsaSzemeredi.f_of_le (by simp; omega)]
  obtain ⟨G, iG, hGc, hG⟩ := ruzsaSzemerediNumber_spec (α := Fin a)
  obtain ⟨H, iH, hHc, hH⟩ := ruzsaSzemerediNumber_spec (α := Fin b)
  have h := (dsum_ll hG hH).le_ruzsaSzemerediNumber
  have e : ruzsaSzemerediNumber (Fin a ⊕ Fin b) = ruzsaSzemerediNumberNat (a + b) := by
    rw [← ruzsaSzemerediNumberNat_card]; simp
  rw [dsum_card_tri hG hH, hGc, hHc, e] at h
  exact h

/-! ### Graphs given by an adjacency mask -/

namespace Mask

/-- Bit `x * n + y` of the mask `M`: whether `x` and `y` are adjacent. -/
def adjM (M n x y : ℕ) : Bool := M.testBit (x * n + y)

/-- The predicted common neighbour of `x` and `y`: the top bit of the meet of their rows. -/
def thd (M n x y : ℕ) : ℕ := Nat.log2 (((M >>> (x * n)) &&& (M >>> (y * n))) % 2 ^ n)

/-- The check on the mask: irreflexive, symmetric, and the common neighbours of every edge are
exactly the predicted vertex `thd`. -/
def MaskOk (M n : ℕ) : Prop :=
  ∀ x < n, adjM M n x x = false ∧ ∀ y < n, adjM M n x y = adjM M n y x ∧
    (adjM M n x y = true → thd M n x y < n ∧
      ∀ z < n, (adjM M n x z && adjM M n y z) = (z == thd M n x y))

instance (M n : ℕ) : Decidable (MaskOk M n) := by unfold MaskOk; infer_instance

/-- The graph encoded by a mask. -/
def gM (M n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y => adjM M n x y = true

instance (M n : ℕ) : DecidableRel (gM M n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (adjM M n x y = true ∨ adjM M n y x = true)))

theorem gM_adj {M n : ℕ} (h : MaskOk M n) {x y : Fin n} :
    (gM M n).Adj x y ↔ adjM M n x y = true := by
  rw [gM, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h1 | h1⟩
    · exact h1
    · rwa [((h y y.2).2 x x.2).1] at h1
  · intro h1
    refine ⟨fun hxy => ?_, Or.inl h1⟩
    subst hxy
    rw [(h x x.2).1] at h1
    exact Bool.noConfusion h1

theorem ll_gM {M n : ℕ} (h : MaskOk M n) : (gM M n).LocallyLinear := by
  refine ll_of_common fun x y hxy => ?_
  rw [gM_adj h] at hxy
  obtain ⟨ht, hz⟩ := ((h x x.2).2 y y.2).2 hxy
  have e := hz _ ht
  rw [beq_self_eq_true, Bool.and_eq_true] at e
  refine ⟨⟨thd M n x y, ht⟩, (gM_adj h).2 e.1, (gM_adj h).2 e.2, fun w hxw hyw => ?_⟩
  rw [gM_adj h] at hxw hyw
  have e' := hz w w.2
  rw [hxw, hyw, Bool.and_self, eq_comm, beq_iff_eq] at e'
  exact Fin.ext e'

theorem card_gM {M n d : ℕ} (h : MaskOk M n) (hd : ∀ x : Fin n, (gM M n).degree x = d) :
    6 * #((gM M n).cliqueFinset 3) = n * d := by
  have h1 := (ll_gM h).card_edgeFinset
  have h2 := sum_degrees_eq_twice_card_edges (gM M n)
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

/-- `KG(6,2)`: vertex `i` is the `i`-th pair of `{0, …, 5}` in lexicographic order, adjacent iff
disjoint. -/
def MKG : ℕ := 1012045315454360172905361713358041908008924197717441927854111620608

/-- `GQ(2,4)`: vertices `a₀…a₅, b₀…b₅`, then `c_ij` (`i < j`, lexicographic); `aᵢ ~ bⱼ` iff
`i ≠ j`, `aᵢ, bᵢ ~ c_jk` iff `i ∈ {j, k}`, `c_ij ~ c_kl` iff disjoint. -/
def MGQ : ℕ := 53067618229521769046738071573877416778872586263338265013355549100346230972124408789241793385084288113576990963260684376741750278034318370957010413230707409486494262579936661591203694540791800365035368156551509140701056

theorem MKG_ok : MaskOk MKG 15 := by decide +kernel
theorem MKG_deg : ∀ x : Fin 15, (gM MKG 15).degree x = 6 := by decide +kernel
theorem MGQ_ok : MaskOk MGQ 27 := by decide +kernel
theorem MGQ_deg : ∀ x : Fin 27, (gM MGQ 27).degree x = 10 := by decide +kernel

end Mask

open Mask

theorem f15 : 15 ≤ SqueezeBench.RuzsaSzemeredi.f 15 := by
  have h1 := card_gM MKG_ok MKG_deg
  have h2 := SqueezeBench.RuzsaSzemeredi.le_f_of_locallyLinear (n := 15) (by decide) _
    (ll_gM MKG_ok)
  omega

theorem f27 : 45 ≤ SqueezeBench.RuzsaSzemeredi.f 27 := by
  have h1 := card_gM MGQ_ok MGQ_deg
  have h2 := SqueezeBench.RuzsaSzemeredi.le_f_of_locallyLinear (n := 27) (by decide) _
    (ll_gM MGQ_ok)
  omega

/-! ### Validity of the record -/

/-- One product step: `f n ≥ 6 · T · f ⌊n/a⌋` from `T ≤ f a`. -/
theorem step_le {a T n x : ℕ} (hT : T ≤ SqueezeBench.RuzsaSzemeredi.f a)
    (hx : x ≤ SqueezeBench.RuzsaSzemeredi.f (n / a)) :
    6 * T * x ≤ SqueezeBench.RuzsaSzemeredi.f n :=
  calc 6 * T * x ≤ 6 * SqueezeBench.RuzsaSzemeredi.f a * SqueezeBench.RuzsaSzemeredi.f (n / a) := by
        gcongr
    _ ≤ SqueezeBench.RuzsaSzemeredi.f (a * (n / a)) := six_mul_le a (n / a)
    _ ≤ SqueezeBench.RuzsaSzemeredi.f n := f_le_of_le (Nat.mul_div_le n a)

theorem tAux_le (fuel : ℕ) : ∀ n, tAux fuel n ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  induction fuel with
  | zero => intro n; exact V008.valid n
  | succ fuel ih =>
    intro n
    unfold tAux
    split_ifs with h15 h27
    · exact V008.valid n
    · refine max_le (V008.valid n) (max_le (max_le ?_ ?_) (Nat.zero_le _))
      · exact f15.trans (f_le_of_le (by omega))
      · exact step_le (a := 15) (T := 15) f15 (ih _)
    · refine max_le (V008.valid n) (max_le (max_le ?_ ?_) (max_le ?_ ?_))
      · exact f15.trans (f_le_of_le (by omega))
      · exact step_le (a := 15) (T := 15) f15 (ih _)
      · exact f27.trans (f_le_of_le (by omega))
      · exact step_le (a := 27) (T := 45) f27 (ih _)

theorem le_tAux (fuel n : ℕ) : V008.record n ≤ tAux fuel n := by
  cases fuel with
  | zero => exact le_rfl
  | succ fuel =>
    unfold tAux
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
    · exact le_max_left _ _

theorem tb_le (n : ℕ) : tb n ≤ SqueezeBench.RuzsaSzemeredi.f n := tAux_le n n

theorem sAux_le (k n : ℕ) : sAux k n ≤ SqueezeBench.RuzsaSzemeredi.f n := by
  induction k with
  | zero => exact tb_le n
  | succ k ih =>
    refine max_le ?_ ih
    calc tb (n - n % 3 ^ (k + 1)) + tb (n % 3 ^ (k + 1))
        ≤ SqueezeBench.RuzsaSzemeredi.f (n - n % 3 ^ (k + 1)) +
          SqueezeBench.RuzsaSzemeredi.f (n % 3 ^ (k + 1)) := add_le_add (tb_le _) (tb_le _)
      _ ≤ SqueezeBench.RuzsaSzemeredi.f (n - n % 3 ^ (k + 1) + n % 3 ^ (k + 1)) := add_le _ _
      _ = SqueezeBench.RuzsaSzemeredi.f n := by rw [Nat.sub_add_cancel (Nat.mod_le _ _)]

theorem le_sAux (k n : ℕ) : V008.record n ≤ sAux k n := by
  induction k with
  | zero => exact le_tAux n n
  | succ k ih => exact ih.trans (le_max_right _ _)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.RuzsaSzemeredi.f record :=
  fun n => sAux_le _ n

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.RuzsaSzemeredi.Lower.V008.record record :=
  fun n => le_sAux _ n

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.RuzsaSzemeredi.nMin SqueezeBench.RuzsaSzemeredi.Lower.V008.record record :=
  ⟨15, by decide, by decide +kernel⟩

end SqueezeBench.RuzsaSzemeredi.Lower.V009
