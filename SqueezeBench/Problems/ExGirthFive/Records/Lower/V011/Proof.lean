import SqueezeBench.Problems.ExGirthFive.Records.Lower.V011.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V010.Proof

/-! Record V011 for ExGirthFive, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V011.lean`.

The Hoffman–Singleton graph (Robertson's description): five pentagons `P_h` and five pentagrams
`Q_i` on `ZMod 5`, vertex `j` of `P_h` adjacent to vertex `h·i + j` of `Q_i`. It is `7`-regular on
`50` vertices with `175` edges and girth `5`, the unique `(7,5)`-Moore graph, so `f 50 = 175`. Its
girth is checked by the kernel once (`hs_check`: no two distinct vertices have two common
neighbours, adjacent ones have none). Induced subgraphs inherit the girth condition, so a fixed
ordering `rank` of the vertices gives `50` graphs at once: the one on the first `n` vertices has
`tab[n]` edges, counted by the kernel over the `175` edges (`count_edges`), and is transported into
`Fin m` for every `m ≥ n` by V008's `transport_le`. The ordering (pentagon `0`, pentagram `0`,
pentagon `1`, …, each block in an affine order) was chosen so that the prefixes are dense: the
first `10` vertices are a Petersen graph, the first `40` the `(6,5)`-cage. -/

namespace SqueezeBench.ExGirthFive.Lower.V011

open Finset SimpleGraph SqueezeBench SqueezeBench.ExGirthFive SqueezeBench.ExGirthFive.Lower.V008

-- Vertices: `(false, h, j)` is vertex `j` of the pentagon `h`, `(true, i, j)` vertex `j` of the
-- pentagram `i`.
abbrev HV := Bool × ZMod 5 × ZMod 5

def hsAdj : HV → HV → Bool
  | (false, h, j), (false, h', j') => decide (h = h' ∧ (j' = j + 1 ∨ j = j' + 1))
  | (true, i, j), (true, i', j') => decide (i = i' ∧ (j' = j + 2 ∨ j = j' + 2))
  | (false, h, j), (true, i, c) => decide (c = h * i + j)
  | (true, i, c), (false, h, j) => decide (c = h * i + j)

theorem hsAdj_symm : ∀ x y : HV, hsAdj x y = true → hsAdj y x = true := by decide +kernel

theorem hsAdj_irrefl : ∀ x : HV, hsAdj x x = false := by decide +kernel

def HS : SimpleGraph HV where
  Adj x y := hsAdj x y = true
  symm := ⟨fun x y h => hsAdj_symm x y h⟩
  loopless := ⟨fun x h => by rw [hsAdj_irrefl x] at h; exact Bool.false_ne_true h⟩

theorem HS_adj {x y : HV} : HS.Adj x y ↔ hsAdj x y = true := Iff.rfl

def commonCount (x y : HV) : ℕ := #(univ.filter fun u => hsAdj x u && hsAdj y u)

-- The girth condition, checked by the kernel: `50 · 50` pairs, `50` candidates each.
theorem hs_check : ∀ x y : HV, x ≠ y →
    commonCount x y ≤ 1 ∧ (hsAdj x y = true → commonCount x y = 0) := by
  decide +kernel

theorem HS_noTwo : NoTwoCommonNeighbours HS := by
  intro x y u v hxy huv hxu hyu hxv hyv
  rw [HS_adj] at hxu hyu hxv hyv
  have h := (hs_check x y hxy).1
  have hsub : ({u, v} : Finset HV) ⊆ univ.filter fun w => hsAdj x w && hsAdj y w := by
    intro w hw
    rw [mem_insert, mem_singleton] at hw
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases hw with rfl | rfl
    · rw [hxu, hyu]; rfl
    · rw [hxv, hyv]; rfl
  have := card_le_card hsub
  rw [card_pair huv] at this
  unfold commonCount at h
  omega

theorem HS_cliqueFree : HS.CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  have hne : a ≠ b := HS.ne_of_adj hab
  rw [HS_adj] at hab hac hbc
  have h := (hs_check a b hne).2 hab
  have hc : c ∈ univ.filter fun w => hsAdj a w && hsAdj b w := by
    rw [mem_filter]
    exact ⟨mem_univ _, by rw [hac, hbc]; rfl⟩
  have := card_pos.mpr ⟨c, hc⟩
  unfold commonCount at h
  omega

-- The ordering: block `2h` is the pentagon `h`, block `2i + 1` the pentagram `i`, each block in
-- an affine order `j ↦ a·j + c` chosen (by a small search) to make the prefixes dense.
def aP : ZMod 5 → ZMod 5 := fun h => match h.val with | 0 => 4 | 1 => 1 | 2 => 4 | 3 => 4 | _ => 4
def cP : ZMod 5 → ZMod 5 := fun h => match h.val with | 0 => 2 | 1 => 2 | 2 => 0 | 3 => 0 | _ => 2
def aQ : ZMod 5 → ZMod 5 := fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 2 | 3 => 2 | _ => 2
def cQ : ZMod 5 → ZMod 5 := fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | _ => 1

def rank : HV → ℕ
  | (false, h, j) => 10 * h.val + (aP h * j + cP h).val
  | (true, i, j) => 10 * i.val + 5 + (aQ i * j + cQ i).val

theorem rank_inj : ∀ x y : HV, rank x = rank y → x = y := by decide +kernel

-- The `175` edges: pentagon edges, pentagram edges, and the edges between pentagon `h` and
-- pentagram `i`; each is given as the pair of its endpoints in increasing rank.
abbrev HE := (ZMod 5 × ZMod 5) ⊕ (ZMod 5 × ZMod 5) ⊕ (ZMod 5 × ZMod 5 × ZMod 5)

def sortPair (x y : HV) : HV × HV := if rank x < rank y then (x, y) else (y, x)

def edgeOf : HE → HV × HV
  | .inl (h, j) => sortPair (false, h, j) (false, h, j + 1)
  | .inr (.inl (i, j)) => sortPair (true, i, j) (true, i, j + 2)
  | .inr (.inr (h, i, j)) => sortPair (false, h, j) (true, i, h * i + j)

theorem edgeOf_adj : ∀ e : HE, hsAdj (edgeOf e).1 (edgeOf e).2 = true := by decide +kernel

theorem edgeOf_sorted : ∀ e : HE, rank (edgeOf e).1 < rank (edgeOf e).2 := by decide +kernel

-- `edgeOf` is injective: its image has as many elements as its domain.
theorem edgeOf_img : #((univ : Finset HE).image edgeOf) = 175 := by decide +kernel

theorem card_HE : Fintype.card HE = 175 := by
  simp only [HE, Fintype.card_sum, Fintype.card_prod, ZMod.card]

theorem edgeOf_inj : Function.Injective edgeOf := by
  have h : Set.InjOn edgeOf ↑(univ : Finset HE) := by
    rw [← Finset.card_image_iff, edgeOf_img, card_univ, card_HE]
  intro a b hab
  exact h (mem_coe.mpr (mem_univ a)) (mem_coe.mpr (mem_univ b)) hab

-- The edge and vertex counts of every prefix, by the kernel.
theorem count_edges : ∀ n, n < 51 →
    Fintype.card {e : HE // rank (edgeOf e).2 < n} = tab.getD n 0 := by
  decide +kernel

theorem count_verts : ∀ n, n < 51 → Fintype.card {v : HV // rank v < n} = n := by decide +kernel

-- The graph induced on the first `m ≤ 50` vertices, placed in `n ≥ m` vertices.
theorem prefix_le (m n : ℕ) (hn1 : 1 ≤ n) (hm : m ≤ 50) (hmn : m ≤ n) : tab.getD m 0 ≤ f n := by
  classical
  have hcard : Fintype.card {v : HV // rank v < m} ≤ n := by
    rw [count_verts m (by omega)]; exact hmn
  let F : {e : HE // rank (edgeOf e).2 < m} → Sym2 {v : HV // rank v < m} := fun e =>
    s(⟨(edgeOf e.1).1, lt_trans (edgeOf_sorted e.1) e.2⟩, ⟨(edgeOf e.1).2, e.2⟩)
  have hF : Function.Injective F := by
    intro e e' h
    have h2 := congrArg (Sym2.map Subtype.val) h
    simp only [F, Sym2.map_mk, Sym2.eq_iff] at h2
    rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext (edgeOf_inj (Prod.ext h1 h2))
    · exfalso
      have s1 := edgeOf_sorted e.1
      have s2 := edgeOf_sorted e'.1
      rw [h1, h2] at s1
      omega
  have hE : ∀ e, F e ∈ (HS.comap (Subtype.val : {v : HV // rank v < m} → HV)).edgeSet :=
    fun e => edgeOf_adj e.1
  have := transport_le (HS.comap (Subtype.val : {v : HV // rank v < m} → HV))
    (comap_cliqueFree _ Subtype.val_injective _ HS_cliqueFree)
    (comap_noTwo _ Subtype.val_injective _ HS_noTwo) hn1 hcard F hF hE
  rwa [count_edges m (by omega)] at this

theorem hs_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f hs := by
  intro n
  unfold hs
  split_ifs with h
  · exact prefix_le 50 n (by omega) le_rfl h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [tab]
    · exact prefix_le n n hn (by omega) le_rfl

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V010.valid hs_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V010.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V010.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 50)
    (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V011
