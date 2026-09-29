import SqueezeBench.Problems.Golomb.Records.Lower.V006.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V005.Proof

/-!
# Golomb lower-bound record V006 — validity

Lindström's argument (B. Lindström, *An inequality for B₂-sequences*, J. Combin. Theory 6
(1969) 211–212) with a boundary correction. With the marks sorted as `a₀ < … < a_{m-1}`:

* the differences `a_{i+j} - a_i`, `1 ≤ j ≤ t`, are distinct (Sidon) and positive, so
  `M (M + 1) ≤ 2 ∑` for their number `M = mOf m t` (`card_mul_le_sum`);
* the order-`j` differences telescope, `X_j + ∑_{r<j} a_r = ∑_{r<j} a_{m-j+r}` (`telescope`);
* the first `r + 1` marks span at least `f (r + 1)` (`prefix_le`), and the last `r + 1`
  as well, after the reflection `x ↦ L - x` (`suffix_le`); hence
  `X_j + 2 G j ≤ j L` (`order_le`).

Summing over `j ≤ t` gives the master inequality `M (M + 1) + 4 ∑_{j ≤ t} G j ≤ t (t + 1) L`,
for any valid lower bound `g`. The record feeds it with itself at smaller arguments, which
is sound by induction on the fuel (`core_valid`).
-/

namespace SqueezeBench.Golomb.Lower.V006

open SqueezeBench Finset

/-! ## Sub-rulers -/

theorem isSidon_mono {S T : Finset ℕ} (hT : T ⊆ S) (hS : IsSidon S) : IsSidon T :=
  fun a ha b hb c hc d hd h => hS a (hT ha) b (hT hb) c (hT hc) d (hT hd) h

/-- The reflection `x ↦ L - x` keeps a Sidon set below `L` Sidon. -/
theorem isSidon_reflect {S : Finset ℕ} {L : ℕ} (hS : IsSidon S) (hL : ∀ x ∈ S, x ≤ L) :
    IsSidon (S.image (fun x => L - x)) := by
  intro a ha b hb c hc d hd h
  simp only [mem_image] at ha hb hc hd
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨d', hd', rfl⟩ := hd
  have := hL a' ha'
  have := hL b' hb'
  have := hL c' hc'
  have := hL d' hd'
  rcases hS a' ha' b' hb' c' hc' d' hd' (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
  · right; subst h1; subst h2; exact ⟨rfl, rfl⟩

/-- The marks of a finset, in increasing order. -/
theorem exists_sorted {S : Finset ℕ} {m : ℕ} (h : S.card = m) :
    ∃ a : ℕ → ℕ, (∀ i, i < m → a i ∈ S) ∧ (∀ i j, i < j → j < m → a i < a j) := by
  refine ⟨fun i => if hi : i < m then S.orderEmbOfFin h ⟨i, hi⟩ else 0, ?_, ?_⟩
  · intro i hi
    simp only [dif_pos hi]
    exact S.orderEmbOfFin_mem h _
  · intro i j hij hj
    simp only [dif_pos (show i < m by omega), dif_pos hj]
    exact (S.orderEmbOfFin h).strictMono (Fin.mk_lt_mk.mpr hij)

section Sorted

variable {S : Finset ℕ} {m L : ℕ} {a : ℕ → ℕ}

theorem sorted_inj (hlt : ∀ i j, i < j → j < m → a i < a j) {i j : ℕ} (hi : i < m) (hj : j < m)
    (h : a i = a j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · have := hlt i j h' hj; omega
  · have := hlt j i h' hi; omega

theorem sorted_le (hlt : ∀ i j, i < j → j < m → a i < a j) {i j : ℕ} (hij : i ≤ j) (hj : j < m) :
    a i ≤ a j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact le_of_lt (hlt i j h hj)
  · rw [show i = j by omega]

/-- The first `r + 1` marks form a ruler of length at most `a r`. -/
theorem prefix_le (hsid : IsSidon S) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {r : ℕ} (hr : r < m) : f (r + 1) ≤ a r := by
  refine f_le_of_mem (by simp) ⟨(range (r + 1)).image a, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := sorted_le hlt (show i ≤ r by omega) hr
    rw [mem_range]
    omega
  · rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact sorted_inj hlt (by omega) (by omega) hij
  · refine isSidon_mono ?_ hsid
    intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hmem i (by omega)
  · exact mem_image.mpr ⟨r, by simp, rfl⟩

/-- The marks from `a i` on form a ruler of length at most `L - a i`, after reflection. -/
theorem suffix_le (hsid : IsSidon S) (hS : ∀ x ∈ S, x ≤ L) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {i : ℕ} (hi : i < m) : f (m - i) ≤ L - a i := by
  refine f_le_of_mem (by simp; omega)
    ⟨(Ico i m).image (fun k => L - a k), ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_image, mem_Ico] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have := sorted_le hlt hk.1 hk.2
    rw [mem_range]
    omega
  · rw [card_image_of_injOn, Nat.card_Ico]
    intro k hk k' hk' hkk
    simp only [coe_Ico, Set.mem_Ico] at hk hk'
    have h1 := hS _ (hmem k hk.2)
    have h2 := hS _ (hmem k' hk'.2)
    simp only at hkk
    exact sorted_inj hlt hk.2 hk'.2 (by omega)
  · refine isSidon_mono ?_ (isSidon_reflect hsid hS)
    intro x hx
    simp only [mem_image, mem_Ico] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨a k, hmem k hk.2, rfl⟩
  · exact mem_image.mpr ⟨i, by simp [hi], rfl⟩

/-- The order-`o` differences telescope. -/
theorem telescope (hlt : ∀ i j, i < j → j < m → a i < a j) {o : ℕ} (ho : o ≤ m) :
    (∑ i ∈ range (m - o), (a (i + o) - a i)) + ∑ r ∈ range o, a r
      = ∑ r ∈ range o, a (m - o + r) := by
  have h1 : (∑ i ∈ range (m - o), (a (i + o) - a i)) + ∑ i ∈ range (m - o), a i
      = ∑ i ∈ range (m - o), a (o + i) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl ?_
    intro i hi
    rw [mem_range] at hi
    have := sorted_le hlt (show i ≤ i + o by omega) (show i + o < m by omega)
    rw [add_comm o i]
    omega
  have h2 := sum_range_add a o (m - o)
  have h3 := sum_range_add a (m - o) o
  rw [add_comm o (m - o)] at h2
  omega

/-- The sum of the order-`o` differences, with the boundary correction from `g`. -/
theorem order_le (hsid : IsSidon S) (hS : ∀ x ∈ S, x ≤ L) (hmem : ∀ i, i < m → a i ∈ S)
    (hlt : ∀ i j, i < j → j < m → a i < a j) {g : ℕ → ℕ} (hg : ∀ n, g n ≤ f n)
    {o : ℕ} (ho : o ≤ m) :
    (∑ i ∈ range (m - o), (a (i + o) - a i)) + 2 * ∑ r ∈ range o, g (r + 1) ≤ o * L := by
  have ht := telescope hlt ho
  have hlow : ∑ r ∈ range o, g (r + 1) ≤ ∑ r ∈ range o, a r := by
    refine sum_le_sum ?_
    intro r hr
    rw [mem_range] at hr
    exact le_trans (hg _) (prefix_le hsid hmem hlt (by omega))
  have hrefl : ∑ r ∈ range o, g (r + 1) = ∑ r ∈ range o, g (o - r) := by
    rw [← sum_range_reflect (fun r => g (r + 1)) o]
    refine sum_congr rfl ?_
    intro r hr
    rw [mem_range] at hr
    congr 1
    omega
  have hhigh : ∑ r ∈ range o, (a (m - o + r) + g (o - r)) ≤ ∑ r ∈ range o, L := by
    refine sum_le_sum ?_
    intro r hr
    rw [mem_range] at hr
    have h1 := suffix_le hsid hS hmem hlt (i := m - o + r) (by omega)
    have h2 := hS _ (hmem (m - o + r) (by omega))
    have h3 := hg (m - (m - o + r))
    rw [show m - (m - o + r) = o - r by omega] at h1 h3
    omega
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← hrefl] at hhigh
  omega

end Sorted

/-! ## Distinct positive integers -/

/-- `c` distinct positive integers sum to at least `c (c + 1) / 2`. -/
theorem card_mul_le_sum (X : Finset ℕ) : (∀ x ∈ X, 0 < x) →
    X.card * (X.card + 1) ≤ 2 * ∑ x ∈ X, x := by
  induction X using Finset.induction_on_max with
  | empty => intro _; simp
  | insert x X hlt ih =>
    intro h0
    have hx : x ∉ X := fun hx => lt_irrefl x (hlt x hx)
    rw [card_insert_of_notMem hx, sum_insert hx]
    have ih' := ih (fun y hy => h0 y (mem_insert_of_mem hy))
    have hsub : X ⊆ Finset.Ioo 0 x := by
      intro y hy
      rw [mem_Ioo]
      exact ⟨h0 y (mem_insert_of_mem hy), hlt y hy⟩
    have hc := card_le_card hsub
    rw [Nat.card_Ioo] at hc
    have hx0 := h0 x (mem_insert_self x X)
    have hc' : X.card + 1 ≤ x := by omega
    calc (X.card + 1) * (X.card + 1 + 1) = X.card * (X.card + 1) + 2 * (X.card + 1) := by ring
      _ ≤ 2 * ∑ y ∈ X, y + 2 * x := by omega
      _ = 2 * (x + ∑ y ∈ X, y) := by ring

/-! ## The differences of order at most `t` -/

/-- The index pairs `(j, i)` of the difference `a (i + j + 1) - a i`, of order `j + 1 ≤ t`. -/
def idx (m t : ℕ) : Finset (ℕ × ℕ) := (range t ×ˢ range m).filter (fun p => p.2 + p.1 + 1 < m)

theorem sum_idx (m t : ℕ) (F : ℕ → ℕ → ℕ) :
    ∑ p ∈ idx m t, F p.1 p.2 = ∑ j ∈ range t, ∑ i ∈ range (m - (j + 1)), F j i := by
  rw [idx, sum_filter, sum_product]
  refine sum_congr rfl ?_
  intro j _
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

theorem card_idx {m t : ℕ} (ht : t ≤ m) :
    2 * (idx m t).card + t * (t + 1) = 2 * (t * m) := by
  have h : (idx m t).card = ∑ j ∈ range t, (m - (j + 1)) := by
    rw [card_eq_sum_ones, sum_idx m t (fun _ _ => 1)]
    simp
  rw [h]
  clear h
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    have := ih (by omega)
    have e1 : (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) := by ring
    have e2 : (t + 1) * m = t * m + m := by ring
    rw [e1, e2]
    omega

theorem card_idx_eq {m t : ℕ} (ht : t ≤ m) : (idx m t).card = mOf m t := by
  have h := card_idx ht
  have he : t * (t + 1) / 2 * 2 = t * (t + 1) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self t
    omega
  rw [mOf]
  omega

theorem sum_id_succ (t : ℕ) : 2 * ∑ j ∈ range t, (j + 1) = t * (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    have e : (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) := by ring
    rw [e]
    omega

theorem gsum_eq (g : ℕ → ℕ) (j : ℕ) : gsum g j = ∑ r ∈ range j, g (r + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [gsum, ih, sum_range_succ]

theorem ggsum_eq (g : ℕ → ℕ) (t : ℕ) : ggsum g t = ∑ j ∈ range t, gsum g (j + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ggsum, ih, sum_range_succ]

/-! ## The master inequality -/

theorem master {m L : ℕ} (hL : L ∈ RulerLengths m) {g : ℕ → ℕ} (hg : ∀ n, g n ≤ f n)
    {t : ℕ} (ht : t ≤ m) :
    mOf m t * (mOf m t + 1) + 4 * ggsum g t ≤ t * (t + 1) * L := by
  obtain ⟨S, hsub, hcard, hsid, _⟩ := hL
  have hS : ∀ x ∈ S, x ≤ L := by
    intro x hx
    have := hsub hx
    rw [mem_range] at this
    omega
  obtain ⟨a, hmem, hlt⟩ := exists_sorted hcard
  let D : ℕ × ℕ → ℕ := fun p => a (p.2 + p.1 + 1) - a p.2
  have hpos : ∀ p ∈ idx m t, a p.2 < a (p.2 + p.1 + 1) := by
    intro p hp
    simp only [idx, mem_filter, mem_product, mem_range] at hp
    exact hlt _ _ (by omega) hp.2
  have hinj : Set.InjOn D (idx m t) := by
    intro p hp p' hp' hpp
    have h1 := hpos p hp
    have h2 := hpos p' hp'
    simp only [idx, coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at hp hp'
    simp only [D] at hpp
    rcases hsid _ (hmem _ hp.2) _ (hmem p'.2 (by omega)) _ (hmem _ hp'.2) _
        (hmem p.2 (by omega)) (by omega) with ⟨e1, e2⟩ | ⟨e1, _⟩
    · have i1 := sorted_inj hlt (by omega) (by omega) e2
      have i2 := sorted_inj hlt hp.2 hp'.2 e1
      exact Prod.ext (by omega) (by omega)
    · omega
  have hdist := card_mul_le_sum ((idx m t).image D) (by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hpos p hp
    simp only [D]
    omega)
  rw [card_image_of_injOn hinj, sum_image hinj, card_idx_eq ht] at hdist
  have hsplit : ∑ p ∈ idx m t, D p
      = ∑ j ∈ range t, ∑ i ∈ range (m - (j + 1)), (a (i + (j + 1)) - a i) := by
    rw [sum_idx m t (fun j i => a (i + j + 1) - a i)]
    simp only [add_assoc]
  have horder : ∀ j ∈ range t,
      (∑ i ∈ range (m - (j + 1)), (a (i + (j + 1)) - a i)) + 2 * gsum g (j + 1)
        ≤ (j + 1) * L := by
    intro j hj
    rw [mem_range] at hj
    rw [gsum_eq]
    exact order_le hsid hS hmem hlt hg (by omega)
  have hsum := sum_le_sum horder
  rw [sum_add_distrib, ← mul_sum, ← sum_mul, ← ggsum_eq, ← hsplit] at hsum
  have hid := sum_id_succ t
  have e : t * (t + 1) * L = 2 * ((∑ j ∈ range t, (j + 1)) * L) := by
    rw [← hid]; ring
  rw [e]
  omega

/-! ## The obligations -/

theorem lind_le {g : ℕ → ℕ} (hg : ∀ n, g n ≤ f n) (m t : ℕ) : lind g m t ≤ f m := by
  rw [lind]
  split
  · rename_i h
    refine le_f (by simp; omega) ?_
    intro L hL
    have hmas := master hL hg (t := t) (by omega)
    have hd : 0 < t * (t + 1) := Nat.mul_pos h.1 (by omega)
    have hlt : mOf m t * (mOf m t + 1) + 4 * ggsum g t + (t * (t + 1) - 1)
        < (L + 1) * (t * (t + 1)) := by
      have : (L + 1) * (t * (t + 1)) = t * (t + 1) * L + t * (t + 1) := by ring
      omega
    have := (Nat.div_lt_iff_lt_mul hd).mpr hlt
    omega
  · exact Nat.zero_le _

theorem core_valid : ∀ k m, core k m ≤ f m
  | 0, m => SqueezeBench.Golomb.Lower.V005.valid m
  | k + 1, m => by
    rw [core]
    exact max_le (SqueezeBench.Golomb.Lower.V005.valid m)
      (max_le (lind_le (core_valid k) m _) (lind_le (core_valid k) m _))

theorem core_ge : ∀ k m, SqueezeBench.Golomb.Lower.V005.record m ≤ core k m
  | 0, _ => le_refl _
  | _ + 1, _ => by rw [core]; exact le_max_left _ _

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  fun m => core_valid m m

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V005.record record :=
  fun m => core_ge m m

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V005.record record :=
  ⟨100, by decide, by decide +kernel⟩

end SqueezeBench.Golomb.Lower.V006
