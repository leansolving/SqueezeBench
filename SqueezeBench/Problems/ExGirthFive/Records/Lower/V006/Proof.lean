import SqueezeBench.Problems.ExGirthFive.Records.Lower.V006.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V005.Proof

/-! Record V006 for ExGirthFive, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V006.lean`. -/

namespace SqueezeBench.ExGirthFive.Lower.V006

open Finset SimpleGraph SqueezeBench SqueezeBench.ExGirthFive

-- A block vertex is a point `(x, y)` or a line `y = a x + b` of the affine plane over `ZMod p`.
abbrev Side (p : ℕ) := (ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)

-- A point is adjacent exactly to the lines through it.
def sadj (p : ℕ) : Side p → Side p → Bool
  | .inl P, .inr L => decide (P.2 = L.1 * P.1 + L.2)
  | .inr L, .inl P => decide (P.2 = L.1 * P.1 + L.2)
  | _, _ => false

theorem sadj_symm {p : ℕ} {s t : Side p} (h : sadj p s t = true) : sadj p t s = true := by
  cases s <;> cases t <;> simp_all [sadj]

theorem sadj_inl {p : ℕ} {P : ZMod p × ZMod p} {t : Side p} (h : sadj p (.inl P) t = true) :
    ∃ L, t = .inr L ∧ P.2 = L.1 * P.1 + L.2 := by
  cases t with
  | inl Q => simp [sadj] at h
  | inr L => exact ⟨L, rfl, by simpa [sadj] using h⟩

theorem sadj_inr {p : ℕ} {L : ZMod p × ZMod p} {t : Side p} (h : sadj p (.inr L) t = true) :
    ∃ P, t = .inl P ∧ P.2 = L.1 * P.1 + L.2 := by
  cases t with
  | inl P => exact ⟨P, rfl, by simpa [sadj] using h⟩
  | inr M => simp [sadj] at h

-- `k` disjoint copies of the point–line incidence graph of the affine plane over `ZMod p`.
def PG (k p : ℕ) : SimpleGraph (Fin k × Side p) where
  Adj u v := u.1 = v.1 ∧ sadj p u.2 v.2 = true
  symm := ⟨by
    rintro ⟨i, u⟩ ⟨j, v⟩ ⟨h1, h2⟩
    exact ⟨h1.symm, sadj_symm h2⟩⟩
  loopless := ⟨by
    rintro ⟨i, u⟩ ⟨-, h⟩
    cases u <;> simp [sadj] at h⟩

-- The graph is bipartite between points and lines, so it has no triangle.
theorem PG_cliqueFree (k p : ℕ) : (PG k p).CliqueFree 3 := by
  intro s hs
  obtain ⟨⟨i, ta⟩, ⟨j, tb⟩, ⟨l, tc⟩, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  have h1 := hab.2
  have h2 := hac.2
  have h3 := hbc.2
  cases ta <;> cases tb <;> cases tc <;>
    first
      | (simp [sadj] at h1; done)
      | (simp [sadj] at h2; done)
      | (simp [sadj] at h3; done)

-- Two points lie on at most one common line and two lines meet in at most one point.
theorem PG_noTwo (k p : ℕ) [Fact p.Prime] : NoTwoCommonNeighbours (PG k p) := by
  rintro ⟨i, tx⟩ ⟨j, ty⟩ ⟨a, tu⟩ ⟨b, tv⟩ hxy huv ⟨e1, f1⟩ ⟨e2, f2⟩ ⟨e3, f3⟩ ⟨e4, f4⟩
  have hij : i = j := e1.trans e2.symm
  have hab : a = b := e1.symm.trans e3
  have hx : tx ≠ ty := fun h => hxy (Prod.ext hij h)
  have hu : tu ≠ tv := fun h => huv (Prod.ext hab h)
  cases tx with
  | inl P =>
      -- `x` and `y` are points, `u` and `v` lines through both
      obtain ⟨L, rfl, i1⟩ := sadj_inl f1
      obtain ⟨M, rfl, i3⟩ := sadj_inl f3
      obtain ⟨Q, rfl, i2⟩ := sadj_inr (sadj_symm f2)
      have i4 : Q.2 = M.1 * Q.1 + M.2 := by simpa [sadj] using f4
      have hPQ : P ≠ Q := fun h => hx (by rw [h])
      have hLM : L ≠ M := fun h => hu (by rw [h])
      by_cases hc : P.1 = Q.1
      · exact hPQ (Prod.ext hc (by rw [i1, i2, hc]))
      · have d1 : P.2 - Q.2 = L.1 * (P.1 - Q.1) := by rw [i1, i2]; ring
        have d2 : P.2 - Q.2 = M.1 * (P.1 - Q.1) := by rw [i3, i4]; ring
        have hs1 : L.1 = M.1 :=
          mul_right_cancel₀ (sub_ne_zero.mpr hc) (by rw [← d1, ← d2])
        have hs2 : L.2 = M.2 := by
          have h5 : L.1 * P.1 + L.2 = M.1 * P.1 + M.2 := by rw [← i1]; exact i3
          rw [hs1] at h5
          exact add_left_cancel h5
        exact hLM (Prod.ext hs1 hs2)
  | inr L =>
      -- `x` and `y` are lines, `u` and `v` points on both
      obtain ⟨U, rfl, j1⟩ := sadj_inr f1
      obtain ⟨V, rfl, j3⟩ := sadj_inr f3
      obtain ⟨M, rfl, j2⟩ := sadj_inl (sadj_symm f2)
      have j4 : V.2 = M.1 * V.1 + M.2 := by simpa [sadj] using sadj_symm f4
      have hUV : U ≠ V := fun h => hu (by rw [h])
      have hLM : L ≠ M := fun h => hx (by rw [h])
      have h5 : L.1 * U.1 + L.2 = M.1 * U.1 + M.2 := by rw [← j1]; exact j2
      have h6 : L.1 * V.1 + L.2 = M.1 * V.1 + M.2 := by rw [← j3]; exact j4
      by_cases hc : L.1 = M.1
      · refine hLM (Prod.ext hc ?_)
        rw [hc] at h5
        exact add_left_cancel h5
      · have d1 : (L.1 - M.1) * U.1 = M.2 - L.2 := by linear_combination h5
        have d2 : (L.1 - M.1) * V.1 = M.2 - L.2 := by linear_combination h6
        have e5 : U.1 = V.1 := mul_left_cancel₀ (sub_ne_zero.mpr hc) (d1.trans d2.symm)
        exact hUV (Prod.ext e5 (by rw [j1, j3, e5]))

-- The `k p³` edges of the `k` blocks, indexed by block, slope, intercept and abscissa.
theorem map_card {k p n : ℕ} [NeZero p] (e : (Fin k × Side p) ↪ Fin n)
    [DecidableRel ((PG k p).map e).Adj] : p * p * p * k ≤ #((PG k p).map e).edgeFinset := by
  classical
  set F : Fin k × ZMod p × ZMod p × ZMod p → Sym2 (Fin n) := fun q =>
    s(e (q.1, .inl (q.2.2.2, q.2.1 * q.2.2.2 + q.2.2.1)), e (q.1, .inr (q.2.1, q.2.2.1))) with hF
  have hsub : (univ : Finset (Fin k × ZMod p × ZMod p × ZMod p)).image F ⊆
      ((PG k p).map e).edgeFinset := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨q, -, rfl⟩ := hs
    rw [hF]
    simp only [mem_edgeFinset, mem_edgeSet, SimpleGraph.map_adj]
    exact ⟨(q.1, .inl (q.2.2.2, q.2.1 * q.2.2.2 + q.2.2.1)), (q.1, .inr (q.2.1, q.2.2.1)),
      ⟨rfl, by simp [sadj]⟩, rfl, rfl⟩
  have hinj : Function.Injective F := by
    intro q q' h
    rw [hF] at h
    simp only [Sym2.eq_iff, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨hk, hx, -⟩, -, ha, hb⟩ := h
    exact Prod.ext hk (Prod.ext ha (Prod.ext hb hx))
  calc p * p * p * k
      = #((univ : Finset (Fin k × ZMod p × ZMod p × ZMod p)).image F) := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
        simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
        ring
    _ ≤ #((PG k p).map e).edgeFinset := Finset.card_le_card hsub

-- One prime of the table gives `p³` edges per block of `2p²` vertices.
theorem block_le (p n : ℕ) (hp : p.Prime) : p * p * p * (n / (2 * p * p)) ≤ f n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  classical
  set k := n / (2 * p * p) with hk
  rcases Nat.eq_zero_or_pos k with h0 | hk0
  · rw [h0]
    exact Nat.zero_le _
  haveI : Nonempty (Fin k × Side p) := ⟨⟨⟨0, hk0⟩, .inl (0, 0)⟩⟩
  have hcard : Fintype.card (Fin k × Side p) ≤ n := by
    have hc : Fintype.card (Fin k × Side p) = k * (2 * p * p) := by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, ZMod.card]
      ring
    rw [hc, hk]
    exact Nat.div_mul_le_self _ _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin k × Side p) (β := Fin n) (by simpa using hcard)
  have hn : 0 < n := lt_of_lt_of_le Fintype.card_pos hcard
  refine le_trans (map_card e) (le_f_of_cliqueFree_of_noTwoCommonNeighbours
    (show nMin ≤ n from hn) (cliqueFree_map_iff.mpr (PG_cliqueFree k p)) ?_)
  rintro x y u v hxy huv axu ayu axv ayv
  rw [SimpleGraph.map_adj] at axu ayu axv ayv
  obtain ⟨x1, u1, h1, hx1, hu1⟩ := axu
  obtain ⟨y1, u2, h2, hy1, hu2⟩ := ayu
  obtain ⟨x2, v1, h3, hx2, hv1⟩ := axv
  obtain ⟨y2, v2, h4, hy2, hv2⟩ := ayv
  have ex : x2 = x1 := e.injective (hx2.trans hx1.symm)
  have ey : y2 = y1 := e.injective (hy2.trans hy1.symm)
  have eu : u2 = u1 := e.injective (hu2.trans hu1.symm)
  have ev : v2 = v1 := e.injective (hv2.trans hv1.symm)
  rw [eu] at h2
  rw [ex] at h3
  rw [ey, ev] at h4
  exact PG_noTwo k p x1 y1 u1 v1 (fun h => hxy (by rw [← hx1, ← hy1, h]))
    (fun h => huv (by rw [← hu1, ← hv1, h])) h1 h2 h3 h4

theorem primes_prime : ∀ p ∈ primes, Nat.Prime p := by
  intro p hp
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f blocks := by
  intro n
  have h : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) →
      (l.map fun p => p * p * p * (n / (2 * p * p))).foldr max 0 ≤ f n := by
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons c t ih =>
        exact max_le (block_le c n (hl c (by simp))) (ih fun q hq => hl q (by simp [hq]))
  exact h primes primes_prime

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V005.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V005.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V005.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 549753716738)
    (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V006
