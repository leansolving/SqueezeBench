import SqueezeBench.Problems.Golomb.Records.Lower.V007.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V006.Proof

/-!
# Golomb lower-bound record V007 — validity

Sort the marks as `a₀ < … < a_{m-1}`. A *separated family* of width `w` is a set `Ls` of
start indices such that the intervals `[l, l + w]` lie in `[0, m)` and any two share at most
one index (`l + w ≤ l'` for `l < l'`). No pair of indices lies in two such intervals, so the
differences `a_{l+i+j+1} - a_{l+i}` of order `≤ u` inside the intervals are distinct
(`family_master`). Per interval and order `o = j + 1` they telescope (`order_eq`):

`X_o + ∑_{1 ≤ r < o} b_r = o · (a_{l+w} - a_l)`, `b_r = (a_{l+r} - a_l) + (a_{l+w} - a_{l+w-r})`,

and the `2k` end pieces `[l, l + r]`, `[l + w - r, l + w]` form a separated family of width `r`
when `2 r ≤ w` (`split_sep`), which the induction on the fuel bounds by `H` (`H_le`).

The sorted marks, `telescope`, `card_mul_le_sum`, `idx` and its lemmas are V006's.
-/

namespace SqueezeBench.Golomb.Lower.V007

open SqueezeBench Finset
open SqueezeBench.Golomb.Lower.V006 (isSidon_mono exists_sorted sorted_inj sorted_le telescope
  card_mul_le_sum idx sum_idx card_idx_eq sum_id_succ gsum gsum_eq mOf)

/-- A translate of a subset of a Sidon set is Sidon. -/
theorem isSidon_shift {S U : Finset ℕ} {c : ℕ} (hS : IsSidon S) (hU : U ⊆ S)
    (hc : ∀ x ∈ U, c ≤ x) : IsSidon (U.image (fun x => x - c)) := by
  intro a ha b hb c' hc' d hd h
  simp only [mem_image] at ha hb hc' hd
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c'', hc'', rfl⟩ := hc'
  obtain ⟨d', hd', rfl⟩ := hd
  have := hc a' ha'
  have := hc b' hb'
  have := hc c'' hc''
  have := hc d' hd'
  rcases hS a' (hU ha') b' (hU hb') c'' (hU hc'') d' (hU hd') (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
  · right; subst h1; subst h2; exact ⟨rfl, rfl⟩

theorem bsum_eq (g : ℕ → ℕ) (u : ℕ) : bsum g u = ∑ j ∈ range u, gsum g j := by
  induction u with
  | zero => rfl
  | succ u ih => rw [bsum, ih, sum_range_succ]

section Sorted

variable {S : Finset ℕ} {m : ℕ} {a : ℕ → ℕ}

/-- The marks `a_l, …, a_{l+w}` form a ruler of length `a_{l+w} - a_l`, after translation. -/
theorem interval_le (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {l w : ℕ} (hlw : l + w < m) :
    f (w + 1) ≤ a (l + w) - a l := by
  have hU : (range (w + 1)).image (fun i => a (l + i)) ⊆ S := by
    intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hmem _ (by omega)
  have hc : ∀ x ∈ (range (w + 1)).image (fun i => a (l + i)), a l ≤ x := by
    intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact sorted_le hlt (by omega) (by omega)
  refine f_le_of_mem (by simp)
    ⟨((range (w + 1)).image (fun i => a (l + i))).image (fun x => x - a l), ?_, ?_,
      isSidon_shift hsid hU hc, ?_⟩
  · intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hx
    have := sorted_le hlt (show l + i ≤ l + w by omega) hlw
    rw [mem_range]
    omega
  · rw [card_image_of_injOn, card_image_of_injOn, card_range]
    · intro i hi j hj hij
      simp only [coe_range, Set.mem_Iio] at hi hj
      have := sorted_inj hlt (show l + i < m by omega) (show l + j < m by omega) hij
      omega
    · intro x hx y hy hxy
      have := hc x hx
      have := hc y hy
      simp only at hxy
      omega
  · exact mem_image.mpr ⟨a (l + w), mem_image.mpr ⟨w, by simp, rfl⟩, rfl⟩

/-- Per interval and order `j + 1`, the differences telescope onto the span and the two end
pieces of each size `r + 1 ≤ j`. -/
theorem order_eq (hlt : ∀ i j, i < j → j < m → a i < a j) {l w j : ℕ} (hlw : l + w < m)
    (hj : j + 1 ≤ w) :
    (∑ i ∈ range (w + 1 - (j + 1)), (a (l + i + j + 1) - a (l + i)))
      + ∑ r ∈ range j, ((a (l + (r + 1)) - a l) + (a (l + w) - a (l + w - (r + 1))))
      = (j + 1) * (a (l + w) - a l) := by
  have hlt' : ∀ i i', i < i' → i' < w + 1 → a (l + i) < a (l + i') :=
    fun i i' h h' => hlt _ _ (by omega) (by omega)
  have ht := telescope (a := fun i => a (l + i)) hlt' (o := j + 1) (by omega)
  have e1 : ∑ i ∈ range (w + 1 - (j + 1)), (a (l + (i + (j + 1))) - a (l + i))
      = ∑ i ∈ range (w + 1 - (j + 1)), (a (l + i + j + 1) - a (l + i)) := by
    refine sum_congr rfl ?_
    intro i _
    rw [show l + (i + (j + 1)) = l + i + j + 1 by omega]
  rw [e1] at ht
  have e2 : ∑ r ∈ range (j + 1), a (l + (w + 1 - (j + 1) + r))
      = ∑ r ∈ range (j + 1), a (l + w - r) := by
    rw [← sum_range_reflect (fun r => a (l + w - r)) (j + 1)]
    refine sum_congr rfl ?_
    intro r hr
    rw [mem_range] at hr
    rw [show l + w - (j + 1 - 1 - r) = l + (w + 1 - (j + 1) + r) by omega]
  rw [e2] at ht
  have e3 : ∑ r ∈ range (j + 1), a (l + r)
      = (j + 1) * a l + ∑ r ∈ range j, (a (l + (r + 1)) - a l) := by
    rw [sum_range_succ']
    have : ∑ r ∈ range j, a (l + (r + 1)) = j * a l + ∑ r ∈ range j, (a (l + (r + 1)) - a l) := by
      have h1 : ∑ r ∈ range j, a (l + (r + 1))
          = ∑ r ∈ range j, ((a (l + (r + 1)) - a l) + a l) := by
        refine sum_congr rfl ?_
        intro r hr
        rw [mem_range] at hr
        have := sorted_le hlt (show l ≤ l + (r + 1) by omega) (show l + (r + 1) < m by omega)
        omega
      rw [h1, sum_add_distrib, sum_const, card_range, smul_eq_mul]
      ring
    rw [this, add_zero]
    ring
  have e4 : ∑ r ∈ range (j + 1), a (l + w - r) + ∑ r ∈ range j, (a (l + w) - a (l + w - (r + 1)))
      = (j + 1) * a (l + w) := by
    rw [sum_range_succ', Nat.sub_zero]
    have h1 : ∑ r ∈ range j, a (l + w - (r + 1)) + ∑ r ∈ range j, (a (l + w) - a (l + w - (r + 1)))
        = j * a (l + w) := by
      rw [← sum_add_distrib]
      have : ∀ r ∈ range j, a (l + w - (r + 1)) + (a (l + w) - a (l + w - (r + 1))) = a (l + w) := by
        intro r hr
        rw [mem_range] at hr
        have := sorted_le hlt (show l + w - (r + 1) ≤ l + w by omega) hlw
        omega
      rw [sum_congr rfl this, sum_const, card_range, smul_eq_mul]
    have : (j + 1) * a (l + w) = j * a (l + w) + a (l + w) := by ring
    omega
  have hle := sorted_le hlt (show l ≤ l + w by omega) hlw
  have : (j + 1) * (a (l + w) - a l) + (j + 1) * a l = (j + 1) * a (l + w) := by
    rw [← mul_add, Nat.sub_add_cancel hle]
  rw [sum_add_distrib]
  omega

/-- Start indices of a separated family of width `w`. -/
def Sep (m w : ℕ) (Ls : Finset ℕ) : Prop :=
  (∀ l ∈ Ls, l + w < m) ∧ ∀ l ∈ Ls, ∀ l' ∈ Ls, l < l' → l + w ≤ l'

/-- The `2k` end pieces of size `r + 1` of a separated family form a separated family. -/
theorem split_sep {w r : ℕ} {Ls : Finset ℕ} (hs : Sep m w Ls) (hr : 1 ≤ r) (hrw : 2 * r ≤ w) :
    Sep m r (Ls ∪ Ls.image (· + (w - r)))
      ∧ (Ls ∪ Ls.image (· + (w - r))).card = 2 * Ls.card
      ∧ ∑ x ∈ Ls ∪ Ls.image (· + (w - r)), (a (x + r) - a x)
        = ∑ l ∈ Ls, ((a (l + r) - a l) + (a (l + w) - a (l + w - r))) := by
  obtain ⟨hin, hsep⟩ := hs
  have hdisj : Disjoint Ls (Ls.image (· + (w - r))) := by
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_image] at hx'
    obtain ⟨l, hl, rfl⟩ := hx'
    rcases Nat.lt_trichotomy l (l + (w - r)) with h | h | h
    · have := hsep l hl _ hx h
      omega
    · omega
    · omega
  have hinj : Set.InjOn (· + (w - r)) (Ls : Set ℕ) := by
    intro x _ y _ h
    simp only at h
    omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rw [mem_union, mem_image] at hx
    rcases hx with hx | ⟨l, hl, rfl⟩
    · have := hin x hx; omega
    · have := hin l hl; omega
  · intro x hx y hy hxy
    rw [mem_union, mem_image] at hx hy
    rcases hx with hx | ⟨l, hl, rfl⟩ <;> rcases hy with hy | ⟨l', hl', rfl⟩
    · have := hsep x hx y hy hxy; omega
    · rcases Nat.lt_trichotomy x l' with h | h | h
      · have := hsep x hx l' hl' h; omega
      · omega
      · have := hsep l' hl' x hx h; omega
    · rcases Nat.lt_trichotomy l y with h | h | h
      · have := hsep l hl y hy h; omega
      · omega
      · have := hsep y hy l hl h; omega
    · rcases Nat.lt_trichotomy l l' with h | h | h
      · have := hsep l hl l' hl' h; omega
      · omega
      · omega
  · rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj]
    ring
  · rw [sum_union hdisj, sum_image hinj, ← sum_add_distrib]
    refine sum_congr rfl ?_
    intro l hl
    have := hin l hl
    rw [show l + (w - r) + r = l + w by omega, show l + (w - r) = l + w - r by omega]

/-- Lindström's inequality for a separated family, with the end pieces bounded by `h`. -/
theorem family_master (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {w u : ℕ} {Ls : Finset ℕ} (hs : Sep m w Ls)
    (hu : u ≤ w) (hu2 : 2 * u ≤ w + 2) {h : ℕ → ℕ}
    (hh : ∀ r, 1 ≤ r → 2 * r ≤ w →
      h (r + 1) ≤ ∑ l ∈ Ls, ((a (l + r) - a l) + (a (l + w) - a (l + w - r)))) :
    Ls.card * mOf (w + 1) u * (Ls.card * mOf (w + 1) u + 1) + 2 * bsum (fun i => h (i + 1)) u
      ≤ u * (u + 1) * ∑ l ∈ Ls, (a (l + w) - a l) := by
  obtain ⟨hin, hsep⟩ := hs
  let E := Ls ×ˢ idx (w + 1) u
  let D : ℕ × (ℕ × ℕ) → ℕ := fun p => a (p.1 + p.2.2 + p.2.1 + 1) - a (p.1 + p.2.2)
  have hmemE : ∀ p ∈ E, p.1 ∈ Ls ∧ p.2.1 < u ∧ p.2.2 + p.2.1 + 1 < w + 1 := by
    intro p hp
    simp only [E, idx, mem_product, mem_filter, mem_range] at hp
    exact ⟨hp.1, hp.2.1.1, hp.2.2⟩
  have hpos : ∀ p ∈ E, a (p.1 + p.2.2) < a (p.1 + p.2.2 + p.2.1 + 1) := by
    intro p hp
    obtain ⟨h1, _, h3⟩ := hmemE p hp
    have := hin _ h1
    exact hlt _ _ (by omega) (by omega)
  have hinj : Set.InjOn D E := by
    intro p hp p' hp' hpp
    have q1 := hpos p hp
    have q2 := hpos p' hp'
    obtain ⟨h1, _, h3⟩ := hmemE p hp
    obtain ⟨h1', _, h3'⟩ := hmemE p' hp'
    have hl := hin _ h1
    have hl' := hin _ h1'
    simp only [D] at hpp
    rcases hsid _ (hmem (p.1 + p.2.2 + p.2.1 + 1) (by omega)) _ (hmem (p'.1 + p'.2.2) (by omega))
        _ (hmem (p'.1 + p'.2.2 + p'.2.1 + 1) (by omega)) _ (hmem (p.1 + p.2.2) (by omega))
        (by omega) with ⟨e1, e2⟩ | ⟨e1, _⟩
    · have i1 := sorted_inj hlt (by omega) (by omega) e1
      have i2 := sorted_inj hlt (by omega) (by omega) e2
      have hll : p.1 = p'.1 := by
        rcases Nat.lt_trichotomy p.1 p'.1 with h | h | h
        · have := hsep _ h1 _ h1' h; omega
        · exact h
        · have := hsep _ h1' _ h1 h; omega
      exact Prod.ext hll (Prod.ext (by omega) (by omega))
    · omega
  have hdist := card_mul_le_sum (E.image D) (by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hpos p hp
    simp only [D]
    omega)
  rw [card_image_of_injOn hinj, sum_image hinj] at hdist
  have hcard : E.card = Ls.card * mOf (w + 1) u := by
    simp only [E]
    rw [card_product, card_idx_eq (by omega)]
  rw [hcard] at hdist
  have hsplit : ∑ p ∈ E, D p = ∑ l ∈ Ls, ∑ j ∈ range u,
      ∑ i ∈ range (w + 1 - (j + 1)), (a (l + i + j + 1) - a (l + i)) := by
    simp only [E, D]
    rw [sum_product]
    refine sum_congr rfl ?_
    intro l _
    exact sum_idx (w + 1) u (fun j i => a (l + i + j + 1) - a (l + i))
  have hper : ∀ l ∈ Ls, (∑ j ∈ range u,
      ∑ i ∈ range (w + 1 - (j + 1)), (a (l + i + j + 1) - a (l + i)))
      + ∑ j ∈ range u, ∑ r ∈ range j, ((a (l + (r + 1)) - a l) + (a (l + w) - a (l + w - (r + 1))))
      = (∑ j ∈ range u, (j + 1)) * (a (l + w) - a l) := by
    intro l hl
    rw [← sum_add_distrib, sum_mul]
    refine sum_congr rfl ?_
    intro j hj
    rw [mem_range] at hj
    exact order_eq hlt (hin l hl) (by omega)
  have htot := sum_congr rfl hper
  rw [sum_add_distrib, ← hsplit, ← mul_sum] at htot
  have hbd : bsum (fun i => h (i + 1)) u ≤ ∑ l ∈ Ls, ∑ j ∈ range u,
      ∑ r ∈ range j, ((a (l + (r + 1)) - a l) + (a (l + w) - a (l + w - (r + 1)))) := by
    rw [bsum_eq, sum_comm]
    refine sum_le_sum ?_
    intro j hj
    rw [mem_range] at hj
    rw [gsum_eq, sum_comm]
    refine sum_le_sum ?_
    intro r hr
    rw [mem_range] at hr
    exact hh (r + 1) (by omega) (by omega)
  have hid := sum_id_succ u
  have e : u * (u + 1) * ∑ l ∈ Ls, (a (l + w) - a l)
      = 2 * ((∑ j ∈ range u, (j + 1)) * ∑ l ∈ Ls, (a (l + w) - a l)) := by
    rw [← hid]; ring
  rw [e]
  omega

theorem lindK_le (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {w : ℕ} {Ls : Finset ℕ} (hs : Sep m w Ls)
    {h : ℕ → ℕ}
    (hh : ∀ r, 1 ≤ r → 2 * r ≤ w →
      h (r + 1) ≤ ∑ l ∈ Ls, ((a (l + r) - a l) + (a (l + w) - a (l + w - r)))) (u : ℕ) :
    lindK h Ls.card (w + 1) u ≤ ∑ l ∈ Ls, (a (l + w) - a l) := by
  rw [lindK]
  split
  · rename_i hc
    have hmas := family_master hsid hmem hlt hs (u := u) (by omega) (by omega) hh
    have hd : 0 < u * (u + 1) := Nat.mul_pos hc.1 (by omega)
    have hlt2 : Ls.card * mOf (w + 1) u * (Ls.card * mOf (w + 1) u + 1)
        + 2 * bsum (fun i => h (i + 1)) u + (u * (u + 1) - 1)
        < (∑ l ∈ Ls, (a (l + w) - a l) + 1) * (u * (u + 1)) := by
      have : (∑ l ∈ Ls, (a (l + w) - a l) + 1) * (u * (u + 1))
          = u * (u + 1) * ∑ l ∈ Ls, (a (l + w) - a l) + u * (u + 1) := by ring
      omega
    have := (Nat.div_lt_iff_lt_mul hd).mpr hlt2
    omega
  · exact Nat.zero_le _

/-- The joint bound: `H` bounds the total span of every separated family. -/
theorem H_le (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) :
    ∀ fuel w (Ls : Finset ℕ), Sep m w Ls → H fuel Ls.card (w + 1) ≤ ∑ l ∈ Ls, (a (l + w) - a l) := by
  have hbase : ∀ w (Ls : Finset ℕ), Sep m w Ls →
      Ls.card * SqueezeBench.Golomb.Lower.V006.record (w + 1) ≤ ∑ l ∈ Ls, (a (l + w) - a l) := by
    intro w Ls hs
    have := card_nsmul_le_sum Ls (fun l => a (l + w) - a l)
      (SqueezeBench.Golomb.Lower.V006.record (w + 1)) (by
        intro l hl
        exact le_trans (SqueezeBench.Golomb.Lower.V006.valid (w + 1))
          (interval_le hsid hmem hlt (hs.1 l hl)))
    rwa [smul_eq_mul] at this
  intro fuel
  induction fuel with
  | zero =>
    intro w Ls hs
    rw [H]
    exact hbase w Ls hs
  | succ fuel ih =>
    intro w Ls hs
    have hh : ∀ r, 1 ≤ r → 2 * r ≤ w → H fuel (2 * Ls.card) (r + 1)
        ≤ ∑ l ∈ Ls, ((a (l + r) - a l) + (a (l + w) - a (l + w - r))) := by
      intro r hr hrw
      obtain ⟨hs', hc', hsum'⟩ := split_sep (a := a) hs hr hrw
      rw [← hc', ← hsum']
      exact ih r _ hs'
    rw [H]
    refine max_le (hbase w Ls hs) (max_le (max_le ?_ ?_) (max_le ?_ ?_)) <;>
      exact lindK_le hsid hmem hlt hs hh _

end Sorted

/-! ## The obligations -/

theorem record_le (m : ℕ) : record m ≤ f m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    show H 0 1 0 ≤ f 0
    rw [H, one_mul]
    exact SqueezeBench.Golomb.Lower.V006.valid 0
  · refine le_f (by simp; omega) ?_
    intro L hL
    obtain ⟨S, hsub, hcard, hsid, _⟩ := hL
    have hS : ∀ x ∈ S, x ≤ L := by
      intro x hx
      have := hsub hx
      rw [mem_range] at this
      omega
    obtain ⟨a, hmem, hlt⟩ := exists_sorted hcard
    have hs : Sep m (m - 1) {0} := ⟨by simp; omega, by simp⟩
    have := H_le hsid hmem hlt m (m - 1) {0} hs
    rw [card_singleton, sum_singleton, show m - 1 + 1 = m by omega, zero_add] at this
    have := hS _ (hmem (m - 1) (by omega))
    show H m 1 m ≤ L
    omega

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record := record_le

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V006.record record := by
  intro m
  show SqueezeBench.Golomb.Lower.V006.record m ≤ H m 1 m
  rcases m with _ | m
  · rw [H, one_mul]
  · rw [H, one_mul]
    exact le_max_left _ _

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V006.record record :=
  ⟨100, by decide, by decide +kernel⟩

end SqueezeBench.Golomb.Lower.V007
