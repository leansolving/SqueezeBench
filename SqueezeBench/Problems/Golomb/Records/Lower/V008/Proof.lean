import SqueezeBench.Problems.Golomb.Records.Lower.V008.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V007.Proof

/-!
# Golomb lower-bound record V008 — validity

Sorted marks `a₀ < … < a_{m-1}`, span `a_{m-1} - a₀`, end spans
`bb r = (a_r - a₀) + (a_{m-1} - a_{m-1-r})`. A pair `(i, i + j + 1)` is indexed by `(j, i)` as in
V006, and `F m u s` is the index set of `E(u, s)`: order `≤ u`, or inside the first `s`
marks, or inside the last `s` marks. Its differences are distinct (Sidon), so
`n (n + 1) ≤ 2 ∑_F D` (`card_mul_le_sum`).

`ext_id` computes `∑_F D` exactly, by induction on `s`: for `s = u + 1` it is the Lindström set
(V007's `order_eq`, summed), and going from `s` to `s + 1` adds the `s - u` pairs ending at
`a_s` and the `s - u` pairs starting at `a_{m-1-s}`, which together with `∑_{r < s-u} bb r`
make `(s - u) bb s`, term by term.

`cert_sum` adds the item inequalities of a certificate, and `certBound_le` uses the check
`POS_r ≤ NEG_r` and V007's `H_le` for two separated intervals, `bLow m r ≤ bb r`.
-/

namespace SqueezeBench.Golomb.Lower.V008

open SqueezeBench Finset
open SqueezeBench.Golomb.Lower.V006 (exists_sorted sorted_inj sorted_le card_mul_le_sum idx sum_idx
  card_idx_eq sum_id_succ mOf)
open SqueezeBench.Golomb.Lower.V007 (order_eq Sep H_le)

/-- The index set of `E(u, s)`; `(j, i)` stands for the pair `(i, i + j + 1)`. -/
def F (m u s : ℕ) : Finset (ℕ × ℕ) :=
  (range m ×ˢ range m).filter
    (fun p => p.2 + p.1 + 1 < m ∧ (p.1 < u ∨ p.2 + p.1 + 1 < s ∨ m - s ≤ p.2))

/-- The difference of the pair indexed by `p`. -/
def D (a : ℕ → ℕ) (p : ℕ × ℕ) : ℕ := a (p.2 + p.1 + 1) - a p.2

/-- The total span of the first and the last `r + 1` marks. -/
def bb (a : ℕ → ℕ) (m r : ℕ) : ℕ := (a r - a 0) + (a (m - 1) - a (m - 1 - r))

theorem F_base {m u : ℕ} (hu : u < m) : F m u (u + 1) = idx m u := by
  ext p
  simp only [F, idx, mem_filter, mem_product, mem_range]
  omega

/-- `∑_{j<u} ∑_{r<j} g (r + 1) = ∑_r (u - r) g r` when `g 0 = 0`. -/
theorem double_sum (g : ℕ → ℕ) (hg : g 0 = 0) {R : ℕ} :
    ∀ u, u ≤ R → ∑ j ∈ range u, ∑ r ∈ range j, g (r + 1) = ∑ r ∈ range R, (u - r) * g r := by
  intro u
  induction u with
  | zero => intro _; simp
  | succ u ih =>
    intro hu
    rw [sum_range_succ, ih (by omega)]
    have h1 : ∑ r ∈ range R, (u + 1 - r) * g r
        = ∑ r ∈ range R, ((u - r) * g r + (if r < u + 1 then g r else 0)) := by
      refine sum_congr rfl ?_
      intro r _
      split_ifs with h
      · rw [show u + 1 - r = (u - r) + 1 by omega, add_mul, one_mul]
      · rw [show u + 1 - r = 0 by omega, show u - r = 0 by omega]; simp
    have h2 : ∑ r ∈ range R, (if r < u + 1 then g r else 0) = ∑ r ∈ range (u + 1), g r := by
      rw [← sum_filter]
      congr 1
      ext r
      simp only [mem_filter, mem_range]
      omega
    rw [h1, sum_add_distrib, h2, sum_range_succ', hg, add_zero]

section Sorted

variable {S : Finset ℕ} {m : ℕ} {a : ℕ → ℕ}

theorem bb_zero : bb a m 0 = 0 := by simp [bb]

theorem D_injOn (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) (u s : ℕ) : Set.InjOn (D a) (F m u s) := by
  intro p hp p' hp' hpp
  simp only [F, coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at hp hp'
  have h1 := hlt p.2 (p.2 + p.1 + 1) (by omega) hp.2.1
  have h2 := hlt p'.2 (p'.2 + p'.1 + 1) (by omega) hp'.2.1
  simp only [D] at hpp
  rcases hsid _ (hmem _ hp.2.1) _ (hmem p'.2 (by omega)) _ (hmem _ hp'.2.1) _
      (hmem p.2 (by omega)) (by omega) with ⟨e1, e2⟩ | ⟨e1, _⟩
  · have i1 := sorted_inj hlt (by omega) (by omega) e2
    have i2 := sorted_inj hlt hp.2.1 hp'.2.1 e1
    exact Prod.ext (by omega) (by omega)
  · omega

/-- The Lindström set: the base case of `ext_id`. -/
theorem lind_id (hlt : ∀ i j, i < j → j < m → a i < a j) {u R : ℕ} (hu : u < m)
    (huR : u ≤ R) :
    ∑ p ∈ idx m u, D a p + ∑ r ∈ range R, (u - r) * bb a m r
      = (∑ j ∈ range u, (j + 1)) * (a (m - 1) - a 0) := by
  have hsplit : ∑ p ∈ idx m u, D a p
      = ∑ j ∈ range u, ∑ i ∈ range (m - (j + 1)), (a (i + j + 1) - a i) :=
    sum_idx m u (fun j i => a (i + j + 1) - a i)
  have hper : ∀ j ∈ range u, (∑ i ∈ range (m - (j + 1)), (a (i + j + 1) - a i))
      + ∑ r ∈ range j, bb a m (r + 1) = (j + 1) * (a (m - 1) - a 0) := by
    intro j hj
    rw [mem_range] at hj
    have h := order_eq hlt (l := 0) (w := m - 1) (j := j) (by omega) (by omega)
    simp only [zero_add] at h
    rw [show m - 1 + 1 - (j + 1) = m - (j + 1) by omega] at h
    exact h
  have htot := sum_congr rfl hper
  rw [sum_add_distrib, ← sum_mul, ← hsplit,
    double_sum (bb a m) bb_zero u huR] at htot
  exact htot

theorem negC_succ (u s r : ℕ) :
    negC u (s + 1) r = negC u s r + (if r < s - u then 1 else 0) := by
  simp only [negC]
  split_ifs <;> omega

theorem posC_succ {u s : ℕ} (hs : u + 1 ≤ s) (r : ℕ) :
    posC u (s + 1) r = posC u s r + (if r = s then s - u else 0) := by
  simp only [posC]
  by_cases h1 : r < s
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; simp
  · by_cases h2 : r = s
    · subst h2; simp
    · rw [if_neg (by omega), if_neg h1, if_neg h2]

/-- The sum over `E(u, s)` in terms of the span and the end spans, and its size. -/
theorem ext_id (hlt : ∀ i j, i < j → j < m → a i < a j) {u R : ℕ} (hu1 : 1 ≤ u) :
    ∀ s, u + 1 ≤ s → s ≤ m → (s = u + 1 ∨ 2 * s ≤ m) → s ≤ R →
      ∑ p ∈ F m u s, D a p + ∑ r ∈ range R, negC u s r * bb a m r
        = (∑ j ∈ range u, (j + 1)) * (a (m - 1) - a 0) + ∑ r ∈ range R, posC u s r * bb a m r
      ∧ (F m u s).card = nOf m u s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro hsm _ hsR
    rw [F_base (by omega)]
    have hneg : ∀ r, negC u (u + 1) r = u - r := by intro r; simp only [negC]; omega
    have hpos : ∀ r, posC u (u + 1) r = 0 := by
      intro r; simp only [posC]; split_ifs <;> omega
    simp only [hneg, hpos, zero_mul, sum_const_zero, add_zero]
    refine ⟨lind_id hlt (by omega) (by omega), ?_⟩
    rw [card_idx_eq (by omega), nOf]
    simp
  | succ s hs ih =>
    intro hsm hcase hsR
    have h2s : 2 * (s + 1) ≤ m := by omega
    obtain ⟨ihs, ihc⟩ := ih (by omega) (Or.inr (by omega)) (by omega)
    let NL := (range (s - u)).image (fun i => (s - 1 - i, i))
    let NR := (range (s - u)).image (fun i => (s - 1 - i, m - 1 - s))
    have hF : F m u (s + 1) = (F m u s ∪ NL) ∪ NR := by
      ext ⟨j, i⟩
      simp only [F, NL, NR, mem_union, mem_filter, mem_product, mem_range, mem_image,
        Prod.mk.injEq]
      constructor
      · intro h
        by_cases h0 : (j < m ∧ i < m) ∧ i + j + 1 < m ∧ (j < u ∨ i + j + 1 < s ∨ m - s ≤ i)
        · exact Or.inl (Or.inl h0)
        · by_cases h3 : i + j + 1 = s
          · exact Or.inl (Or.inr ⟨i, by omega, by omega, rfl⟩)
          · exact Or.inr ⟨s - 1 - j, by omega, by omega, by omega⟩
      · rintro ((h | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) <;> omega
    have hd1 : Disjoint (F m u s) NL := by
      rw [disjoint_left]
      intro p hp hp'
      simp only [NL, mem_image, mem_range] at hp'
      obtain ⟨k, hk, rfl⟩ := hp'
      simp only [F, mem_filter, mem_product, mem_range] at hp
      omega
    have hd2 : Disjoint (F m u s ∪ NL) NR := by
      rw [disjoint_left]
      intro p hp hp'
      simp only [NR, mem_image, mem_range] at hp'
      obtain ⟨k, hk, rfl⟩ := hp'
      rw [mem_union] at hp
      rcases hp with hp | hp
      · simp only [F, mem_filter, mem_product, mem_range] at hp
        omega
      · simp only [NL, mem_image, mem_range, Prod.mk.injEq] at hp
        omega
    have hiL : Set.InjOn (fun i => (s - 1 - i, i)) (range (s - u) : Set ℕ) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact h.2
    have hiR : Set.InjOn (fun i => (s - 1 - i, m - 1 - s)) (range (s - u) : Set ℕ) := by
      intro x hx y hy h
      simp only [coe_range, Set.mem_Iio] at hx hy
      simp only [Prod.mk.injEq] at h
      omega
    have hsumL : ∑ p ∈ NL, D a p = ∑ i ∈ range (s - u), (a s - a i) := by
      simp only [NL]
      rw [sum_image hiL]
      refine sum_congr rfl ?_
      intro i hi
      rw [mem_range] at hi
      simp only [D]
      rw [show i + (s - 1 - i) + 1 = s by omega]
    have hsumR : ∑ p ∈ NR, D a p = ∑ i ∈ range (s - u), (a (m - 1 - i) - a (m - 1 - s)) := by
      simp only [NR]
      rw [sum_image hiR]
      refine sum_congr rfl ?_
      intro i hi
      rw [mem_range] at hi
      simp only [D]
      rw [show m - 1 - s + (s - 1 - i) + 1 = m - 1 - i by omega]
    have hterm : ∀ i ∈ range (s - u),
        (a s - a i) + (a (m - 1 - i) - a (m - 1 - s)) + bb a m i = bb a m s := by
      intro i hi
      rw [mem_range] at hi
      simp only [bb]
      have := sorted_le hlt (show 0 ≤ i by omega) (show i < m by omega)
      have := sorted_le hlt (show i ≤ s by omega) (show s < m by omega)
      have := sorted_le hlt (show m - 1 - s ≤ m - 1 - i by omega) (show m - 1 - i < m by omega)
      have := sorted_le hlt (show m - 1 - i ≤ m - 1 by omega) (show m - 1 < m by omega)
      omega
    have hnew := sum_congr rfl hterm
    rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, smul_eq_mul] at hnew
    have hnegs : ∑ r ∈ range R, negC u (s + 1) r * bb a m r
        = ∑ r ∈ range R, negC u s r * bb a m r + ∑ r ∈ range (s - u), bb a m r := by
      have : ∑ r ∈ range R, (if r < s - u then 1 else 0) * bb a m r
          = ∑ r ∈ range (s - u), bb a m r := by
        simp only [ite_mul, one_mul, zero_mul]
        rw [← sum_filter]
        congr 1
        ext r
        simp only [mem_filter, mem_range]
        omega
      rw [← this, ← sum_add_distrib]
      refine sum_congr rfl ?_
      intro r _
      rw [negC_succ, add_mul]
    have hposs : ∑ r ∈ range R, posC u (s + 1) r * bb a m r
        = ∑ r ∈ range R, posC u s r * bb a m r + (s - u) * bb a m s := by
      have : ∑ r ∈ range R, (if r = s then s - u else 0) * bb a m r = (s - u) * bb a m s := by
        simp only [ite_mul, zero_mul]
        rw [sum_ite_eq' (range R) s (fun r => (s - u) * bb a m r)]
        rw [if_pos (mem_range.mpr (by omega))]
      rw [← this, ← sum_add_distrib]
      refine sum_congr rfl ?_
      intro r _
      rw [posC_succ (by omega), add_mul]
    refine ⟨?_, ?_⟩
    · rw [hF, sum_union hd2, sum_union hd1, hsumL, hsumR, hnegs, hposs]
      omega
    · rw [hF, card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_image_of_injOn hiL,
        card_image_of_injOn hiR, card_range, ihc, nOf, nOf]
      obtain ⟨d, rfl⟩ : ∃ d, s = u + 1 + d := ⟨s - (u + 1), by omega⟩
      rw [show u + 1 + d + 1 - 1 - u = d + 1 by omega, show u + 1 + d + 1 - u = d + 2 by omega,
        show u + 1 + d - 1 - u = d by omega, show u + 1 + d - u = d + 1 by omega]
      ring

/-- The inequality of one extended set. -/
theorem item_le (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {u s R : ℕ} (hu1 : 1 ≤ u) (hus : u + 1 ≤ s)
    (hsm : s ≤ m) (hcase : s = u + 1 ∨ 2 * s ≤ m) (hsR : s ≤ R) :
    nOf m u s * (nOf m u s + 1) + 2 * ∑ r ∈ range R, negC u s r * bb a m r
      ≤ u * (u + 1) * (a (m - 1) - a 0) + 2 * ∑ r ∈ range R, posC u s r * bb a m r := by
  obtain ⟨hid, hcard⟩ := ext_id hlt hu1 s hus hsm hcase hsR
  have hinj := D_injOn hsid hmem hlt u s
  have hdist := card_mul_le_sum ((F m u s).image (D a)) (by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    simp only [F, mem_filter, mem_product, mem_range] at hp
    have := hlt p.2 (p.2 + p.1 + 1) (by omega) hp.2.1
    simp only [D]
    omega)
  rw [card_image_of_injOn hinj, sum_image hinj, hcard] at hdist
  have hT := sum_id_succ u
  have e : u * (u + 1) * (a (m - 1) - a 0)
      = 2 * ((∑ j ∈ range u, (j + 1)) * (a (m - 1) - a 0)) := by rw [← hT]; ring
  rw [e]
  omega

/-- The weighted sum of the item inequalities of a certificate. -/
theorem cert_sum (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {R : ℕ} :
    ∀ cs : List (ℕ × ℕ × ℕ), (∀ c ∈ cs, okItem m c = true) → (∀ c ∈ cs, c.2.2 ≤ R) →
      numS m cs + 2 * ∑ r ∈ range R, negS cs r * bb a m r
        ≤ denS cs * (a (m - 1) - a 0) + 2 * ∑ r ∈ range R, posS cs r * bb a m r := by
  intro cs
  induction cs with
  | nil => intro _ _; simp [numS, negS, posS, denS]
  | cons c cs ih =>
    intro hok hR
    have ih' := ih (fun c' hc' => hok c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hR c' (List.mem_cons_of_mem c hc'))
    have hc := hok c List.mem_cons_self
    simp only [okItem, decide_eq_true_eq] at hc
    have hit := item_le (R := R) hsid hmem hlt hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      (hR c List.mem_cons_self)
    have hit' := Nat.mul_le_mul_left c.1 hit
    simp only [numS, negS, posS, denS, List.map_cons, List.sum_cons] at ih' ⊢
    have en : ∑ r ∈ range R, (c.1 * negC c.2.1 c.2.2 r
          + (cs.map fun c => c.1 * negC c.2.1 c.2.2 r).sum) * bb a m r
        = c.1 * ∑ r ∈ range R, negC c.2.1 c.2.2 r * bb a m r
          + ∑ r ∈ range R, (cs.map fun c => c.1 * negC c.2.1 c.2.2 r).sum * bb a m r := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl ?_
      intro r _
      ring
    have ep : ∑ r ∈ range R, (c.1 * posC c.2.1 c.2.2 r
          + (cs.map fun c => c.1 * posC c.2.1 c.2.2 r).sum) * bb a m r
        = c.1 * ∑ r ∈ range R, posC c.2.1 c.2.2 r * bb a m r
          + ∑ r ∈ range R, (cs.map fun c => c.1 * posC c.2.1 c.2.2 r).sum * bb a m r := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl ?_
      intro r _
      ring
    rw [en, ep]
    linarith [hit', ih']

/-- V007's bound for the two separated end intervals of `r + 1` marks. -/
theorem bLow_le (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) (r : ℕ) : bLow m r ≤ bb a m r := by
  rw [bLow]
  split
  · exact Nat.zero_le _
  · rename_i h
    have hne : (0 : ℕ) ≠ m - 1 - r := by omega
    have hs : Sep m r {0, m - 1 - r} := by
      refine ⟨?_, ?_⟩
      · intro l hl
        simp only [mem_insert, mem_singleton] at hl
        omega
      · intro l hl l' hl' hll
        simp only [mem_insert, mem_singleton] at hl hl'
        omega
    have := H_le hsid hmem hlt (r + 1) r {0, m - 1 - r} hs
    rw [card_pair hne, sum_pair hne, zero_add, show m - 1 - r + r = m - 1 by omega] at this
    exact this

/-- A checked certificate bounds the span. -/
theorem certBound_le_span (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) (R : ℕ) (cs : List (ℕ × ℕ × ℕ)) :
    certBound m R cs ≤ a (m - 1) - a 0 := by
  rw [certBound]
  split
  · rename_i hok
    simp only [certOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range]
      at hok
    obtain ⟨⟨⟨hitems, hR⟩, hcheck⟩, hden⟩ := hok
    have hsum := cert_sum (R := R) hsid hmem hlt cs hitems hR
    have hterm : ∀ r ∈ range R, (negS cs r - posS cs r) * bLow m r + posS cs r * bb a m r
        ≤ negS cs r * bb a m r := by
      intro r hr
      rw [mem_range] at hr
      have h1 := hcheck r hr
      have h2 := bLow_le hsid hmem hlt (m := m) r
      calc (negS cs r - posS cs r) * bLow m r + posS cs r * bb a m r
          ≤ (negS cs r - posS cs r) * bb a m r + posS cs r * bb a m r :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ h2) _
        _ = negS cs r * bb a m r := by rw [← add_mul, Nat.sub_add_cancel h1]
    have hle := sum_le_sum hterm
    rw [sum_add_distrib] at hle
    have hlt2 : numS m cs + 2 * ∑ r ∈ range R, (negS cs r - posS cs r) * bLow m r
        + (denS cs - 1) < (a (m - 1) - a 0 + 1) * denS cs := by
      have : (a (m - 1) - a 0 + 1) * denS cs = denS cs * (a (m - 1) - a 0) + denS cs := by ring
      omega
    have := (Nat.div_lt_iff_lt_mul hden).mpr hlt2
    omega
  · exact Nat.zero_le _

end Sorted

/-! ## The obligations -/

theorem certBound_le (m R : ℕ) (cs : List (ℕ × ℕ × ℕ)) : certBound m R cs ≤ f m := by
  by_cases hok : certOk m R cs = true
  · have hm : 1 ≤ m := by
      simp only [certOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hitems, _⟩, _⟩, hden⟩ := hok
      rcases cs with _ | ⟨c, cs⟩
      · simp [denS] at hden
      · have := hitems c List.mem_cons_self
        simp only [okItem, decide_eq_true_eq] at this
        omega
    refine le_f (by simp; omega) ?_
    intro L hL
    obtain ⟨S, hsub, hcard, hsid, _⟩ := hL
    have hS : ∀ x ∈ S, x ≤ L := by
      intro x hx
      have := hsub hx
      rw [mem_range] at this
      omega
    obtain ⟨a, hmem, hlt⟩ := exists_sorted hcard
    have h1 := certBound_le_span hsid hmem hlt R cs
    have h2 := hS _ (hmem (m - 1) (by omega))
    omega
  · rw [certBound, if_neg hok]
    exact Nat.zero_le _

theorem cand_le (m s₀ J : ℕ) : cand m s₀ J ≤ f m := by
  rw [cand]
  split
  · exact certBound_le _ _ _
  · exact Nat.zero_le _

theorem wRaw_le (m : ℕ) : wRaw m ≤ f m := by
  simp only [wRaw]
  repeat' apply max_le
  all_goals exact cand_le _ _ _

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  fun m => max_le (SqueezeBench.Golomb.Lower.V007.valid m) (wRaw_le m)

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V007.record record :=
  fun _ => le_max_left _ _

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V007.record record :=
  ⟨100, by decide, by decide +kernel⟩

end SqueezeBench.Golomb.Lower.V008
