import SqueezeBench.Problems.ExGirthFive.Records.Lower.V008.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V007.Proof

/-! Record V008 for ExGirthFive, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V008.lean`.

V006 and V007 use only whole affine planes: `⌊n/(2p²)⌋` copies of the point–line incidence graph
of `AG(2,p)` (without vertical lines), and the `n mod 2p²` leftover vertices stay isolated. Here
the leftover carries an induced subgraph of one more plane: `s` full parallel classes (`s·p`
lines) together with `m` of the points, which has exactly `s·m` edges because every point lies on
exactly one line of each class. With `s = ⌈r/(2p)⌉` and `m = r − s·p` this is about `r²/(4p)`
edges on `r` leftover vertices, while it was `0`. The girth condition is inherited: the block
graph is the pullback (`comap`) of V006's `PG` along an injection, then pushed into `Fin n`. -/

namespace SqueezeBench.ExGirthFive.Lower.V008

open Finset SimpleGraph SqueezeBench SqueezeBench.ExGirthFive SqueezeBench.ExGirthFive.Lower.V006

-- A girth-`5` graph on a finite type with at most `n` vertices and `#I` distinct edges exhibited.
theorem transport_le {V : Type*} [Fintype V] (H : SimpleGraph V)
    (h3 : H.CliqueFree 3) (hH4 : NoTwoCommonNeighbours H) {n : ℕ} (hn : nMin ≤ n)
    (hV : Fintype.card V ≤ n) {I : Type*} [Fintype I] (F : I → Sym2 V)
    (hF : Function.Injective F) (hE : ∀ i, F i ∈ H.edgeSet) : Fintype.card I ≤ f n := by
  classical
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · rw [Fintype.card_eq_zero]; exact Nat.zero_le _
  have hne : Nonempty V := Sym2.ind (fun a _ => ⟨a⟩) (F i₀)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := V) (β := Fin n) (by simpa using hV)
  refine le_trans ?_ (le_f_of_cliqueFree_of_noTwoCommonNeighbours (G := H.map e) hn
    (cliqueFree_map_iff.mpr h3) ?_)
  · have hinj : Function.Injective (fun i => Sym2.map e (F i)) :=
      (Sym2.map.injective e.injective).comp hF
    calc Fintype.card I = #((univ : Finset I).image fun i => Sym2.map e (F i)) := by
          rw [card_image_of_injective _ hinj, card_univ]
      _ ≤ #(H.map e).edgeFinset := by
          refine card_le_card ?_
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨i, -, rfl⟩ := hx
          rw [mem_edgeFinset, edgeSet_map]
          exact ⟨F i, hE i, rfl⟩
  · rintro x y u v hxy huv axu ayu axv ayv
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
    exact hH4 x1 y1 u1 v1 (fun h => hxy (by rw [← hx1, ← hy1, h]))
      (fun h => huv (by rw [← hu1, ← hv1, h])) h1 h2 h3 h4

-- Both halves of the girth condition pass to the pullback along an injection.
theorem comap_noTwo {V W : Type*} (φ : V → W) (hφ : Function.Injective φ) (G : SimpleGraph W)
    (h : NoTwoCommonNeighbours G) : NoTwoCommonNeighbours (G.comap φ) :=
  fun _ _ _ _ hxy huv a b c d => h _ _ _ _ (hφ.ne hxy) (hφ.ne huv) a b c d

theorem comap_cliqueFree {V W : Type*} (φ : V → W) (hφ : Function.Injective φ)
    (G : SimpleGraph W) (h : G.CliqueFree 3) : (G.comap φ).CliqueFree 3 :=
  h.comap ⟨(Embedding.comap ⟨φ, hφ⟩ G).toCopy⟩

-- `k` full affine planes over `ZMod p` plus a sub-plane with `s` slope classes and `m` points:
-- `k·2p² + s·p + m` vertices and `k·p³ + s·m` edges.
theorem subplane_le (p : ℕ) (hp : p.Prime) (k s m n : ℕ) (hs : s ≤ p) (hm : m ≤ p * p)
    (hn : k * (2 * p * p) + (s * p + m) ≤ n) : k * (p * p * p) + s * m ≤ f n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  classical
  have hp0 : 0 < p := hp.pos
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have h1 : k * (2 * p * p) = 0 := by omega
    have h2 : s * p = 0 := by omega
    have h3 : m = 0 := by omega
    rcases Nat.mul_eq_zero.mp h1 with hk | hpp
    · rcases Nat.mul_eq_zero.mp h2 with hs0 | hp'
      · simp [hk, hs0, h3]
      · omega
    · have : 0 < 2 * p * p := by positivity
      omega
  obtain ⟨P, -, hP⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset (ZMod p × ZMod p))) (n := m) (by simpa using hm)
  obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset (ZMod p))) (n := s) (by simpa using hs)
  -- the vertices: `k` full blocks, then the chosen points and the lines of the chosen classes
  let φ : (Fin k × Side p ⊕ (P ⊕ A × ZMod p)) → Fin (k + 1) × Side p := fun v =>
    match v with
    | .inl (i, w) => (i.castSucc, w)
    | .inr (.inl q) => (Fin.last k, .inl q.1)
    | .inr (.inr (a, b)) => (Fin.last k, .inr (a.1, b))
  have hφ : Function.Injective φ := by
    have hne : ∀ i : Fin k, i.castSucc ≠ Fin.last k := fun i => (Fin.castSucc_lt_last i).ne
    rintro (⟨i, w⟩ | q | ⟨a, b⟩) (⟨j, w'⟩ | q' | ⟨a', b'⟩) h <;>
      simp only [φ, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
        Fin.castSucc_inj] at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · exact absurd h.1 (hne i)
    · exact absurd h.1 (hne i)
    · exact absurd h.1.symm (hne j)
    · rw [Subtype.ext h.2]
    · exact absurd h.1.symm (hne j)
    · obtain ⟨-, ha, rfl⟩ := h
      rw [Subtype.ext ha]
  -- the edges: `(block, a, b, x)` in a full block, `(point, class)` in the sub-plane
  let F : (Fin k × (ZMod p × ZMod p × ZMod p)) ⊕ (P × A) →
      Sym2 (Fin k × Side p ⊕ (P ⊕ A × ZMod p)) := fun q =>
    match q with
    | .inl (i, a, b, x) => s(.inl (i, .inl (x, a * x + b)), .inl (i, .inr (a, b)))
    | .inr (q, a) => s(.inr (.inl q), .inr (.inr (a, q.1.2 - a.1 * q.1.1)))
  have hF : Function.Injective F := by
    rintro (⟨i, a, b, x⟩ | ⟨q, a⟩) (⟨j, a', b', x'⟩ | ⟨q', a'⟩) h <;>
      simp only [F, Sym2.eq_iff, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        and_false, or_false] at h
    · obtain ⟨⟨rfl, rfl, -⟩, -, rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl, -⟩ := h; rfl
  have hE : ∀ q, F q ∈ ((PG (k + 1) p).comap φ).edgeSet := by
    rintro (⟨i, a, b, x⟩ | ⟨q, a⟩)
    · simp [F, φ, PG, sadj]
    · simp [F, φ, PG, sadj]
  have hcard : Fintype.card (Fin k × Side p ⊕ (P ⊕ A × ZMod p)) ≤ n := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card,
      Fintype.card_coe, hP, hA]
    exact le_of_eq_of_le (by ring) hn
  have := transport_le ((PG (k + 1) p).comap φ)
    (comap_cliqueFree φ hφ _ (PG_cliqueFree (k + 1) p))
    (comap_noTwo φ hφ _ (PG_noTwo (k + 1) p)) hn0 hcard F hF hE
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card,
    Fintype.card_coe, hP, hA] at this
  exact le_of_eq_of_le (by ring) this

-- The sub-plane of `part p r` fits in `r` vertices: `s ≤ p` classes and `m ≤ p²` points.
theorem part_spec (p r : ℕ) (hp : 0 < p) (hr : r < 2 * p * p) :
    ∃ s m, s ≤ p ∧ m ≤ p * p ∧ s * p + m ≤ r ∧ part p r ≤ s * m := by
  have h2p : 0 < 2 * p := by omega
  have hdiv := Nat.div_add_mod (r + 2 * p - 1) (2 * p)
  have hmod := Nat.mod_lt (r + 2 * p - 1) h2p
  have hs_eq : slopes p r = (r + 2 * p - 1) / (2 * p) := rfl
  generalize hs : (r + 2 * p - 1) / (2 * p) = s at hdiv hs_eq
  generalize (r + 2 * p - 1) % (2 * p) = t at hdiv hmod
  have e1 : 2 * p * s = 2 * (s * p) := by ring
  have e2 : 2 * p * p = 2 * (p * p) := by ring
  have hs_le : s ≤ p := by
    have : s < p + 1 := by
      rw [← hs, Nat.div_lt_iff_lt_mul h2p]
      have e3 : (p + 1) * (2 * p) = 2 * p * p + 2 * p := by ring
      rw [e3]
      omega
    omega
  by_cases hc : r < s * p
  · refine ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by simp, ?_⟩
    simp only [part, hs_eq, Nat.sub_eq_zero_of_le hc.le, mul_zero, le_refl]
  · rw [not_lt] at hc
    refine ⟨s, r - s * p, hs_le, by omega, by omega, ?_⟩
    simp only [part, hs_eq, le_refl]

-- One prime of the table: full planes on `⌊n/(2p²)⌋` blocks, a sub-plane on the leftover.
theorem blk_le (p n : ℕ) (hp : p.Prime) : blk p n ≤ f n := by
  have hp0 : 0 < p := hp.pos
  have hpp : 0 < 2 * p * p := by positivity
  obtain ⟨s, m, hs, hm, hsm, hpart⟩ := part_spec p (n % (2 * p * p)) hp0 (Nat.mod_lt _ hpp)
  have hdiv := Nat.div_add_mod n (2 * p * p)
  calc blk p n = (n / (2 * p * p)) * (p * p * p) + part p (n % (2 * p * p)) := by
        rw [blk, mul_comm]
    _ ≤ (n / (2 * p * p)) * (p * p * p) + s * m := Nat.add_le_add_left hpart _
    _ ≤ f n := subplane_le p hp _ s m n hs hm (by nlinarith)

-- The new entries are checked by `norm_num`; the V007 entries were checked in V007.
theorem primes_prime : ∀ p ∈ primes, Nat.Prime p := by
  rw [primes, List.forall_mem_append]
  refine ⟨?_, SqueezeBench.ExGirthFive.Lower.V007.primes_prime⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f blocks := by
  intro n
  have h : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) →
      (l.map fun p => blk p n).foldr max 0 ≤ f n := by
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons c t ih =>
        exact max_le (blk_le c n (hl c (by simp))) (ih fun q hq => hl q (by simp [hq]))
  exact h primes primes_prime

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V007.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V007.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V007.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 1000)
    (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V008
