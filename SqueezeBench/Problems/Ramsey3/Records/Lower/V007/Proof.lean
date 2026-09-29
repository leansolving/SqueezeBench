import SqueezeBench.Problems.Ramsey3.Records.Lower.V007.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V006.Proof

-- Record V007 for Ramsey3, lower direction, by trial claude-fable.
--
-- The ordered incidence graph (Codenotti–Pudlák–Resta 2000; Kostochka–Pudlák–Rödl 2010; in
-- the form used here, Kocbek, arXiv:2507.09235, Definition 2.2 and Theorems 2.3–2.4). For a
-- prime `p`, a flag is `(x, s, b) ∈ (Z/p)³`: the point `(x, s x + b)` on the line `y = s x + b`.
-- Points are ordered by the code `x·p + y ∈ ℕ`. Flags `f, g` are adjacent when their lines
-- differ and the smaller point lies on the line of the other.
--
-- * Triangle-free: adjacency orders the points, so a triangle has points `f < g < h`; then the
--   points of `f` and `g` both lie on the lines of `g` and of `h`, which are distinct — but two
--   distinct points determine at most one non-vertical line (`(s − s')(x − x') = 0` in a
--   field): `two_points`, `no_triangle`.
-- * Independence `≤ |P| + |L| = 2p²`: split an independent set into the flags whose point is
--   the largest of the set on their line (at most one per line) and the rest (at most one per
--   point: a second flag `(p, ℓ')` at the same point would be adjacent to the larger flag
--   `(q, ℓ)` on `ℓ`): `ig_indep_card_le`.
-- * `good_inc p : Good (p³) (2p²)`, transported to `Fin (p³)` by `Fintype.equivFinOfCardEq`.
--
-- The record takes the largest prime `q` with `2q² ≤ k−1` (`isqrt`, `primeBelow`, `isPrime`
-- by trial division, all structurally recursive so the kernel evaluates them) and
-- `Good (q³) (2q²) → Good (q³) (k−1)`. `isPrime_prime` turns the Boolean test into
-- `Nat.Prime`, which makes `ZMod q` a field.

namespace SqueezeBench.Ramsey3.Lower.V007

open SqueezeBench SimpleGraph Finset
open SqueezeBench.Ramsey3.Lower.V005 (GoodOn Good goodOn_comap good_mono good_mono_m good_max
  good_c5)

-- The ordered point–line incidence graph over the prime field `ZMod p`. A flag is a triple
-- `(x, s, b)`: the point `(x, s x + b)` on the non-vertical line `y = s x + b`. Points are
-- ordered by their code `x * p + y` in `ℕ`. Two flags are adjacent when their lines differ
-- and the smaller point lies on the other's line.
section Incidence

variable (p : ℕ) [Fact (Nat.Prime p)]

abbrev Flag := ZMod p × ZMod p × ZMod p

-- The `y`-coordinate of the point of a flag, its line, and the code of its point.
def yc (f : Flag p) : ZMod p := f.2.1 * f.1 + f.2.2

def line (f : Flag p) : ZMod p × ZMod p := f.2

def ptc (f : Flag p) : ℕ := (f.1).val * p + (yc p f).val

-- The point of `f` lies on the line `ℓ`.
def onLine (f : Flag p) (ℓ : ZMod p × ZMod p) : Prop := ℓ.1 * f.1 + ℓ.2 = yc p f

def irel (f g : Flag p) : Prop := line p f ≠ line p g ∧ ptc p f < ptc p g ∧ onLine p f (line p g)

def ig : SimpleGraph (Flag p) := SimpleGraph.fromRel (irel p)

theorem ig_adj (f g : Flag p) : (ig p).Adj f g ↔ f ≠ g ∧ (irel p f g ∨ irel p g f) :=
  SimpleGraph.fromRel_adj _ _ _

-- The point code determines the point.
theorem ptc_inj {f g : Flag p} (h : ptc p f = ptc p g) : f.1 = g.1 ∧ yc p f = yc p g := by
  unfold ptc at h
  have h1 := ZMod.val_lt (f.1)
  have h2 := ZMod.val_lt (g.1)
  have h3 := ZMod.val_lt (yc p f)
  have h4 := ZMod.val_lt (yc p g)
  have hx : (f.1).val = (g.1).val := by
    rcases Nat.lt_trichotomy (f.1).val (g.1).val with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  have hy : (yc p f).val = (yc p g).val := by nlinarith
  exact ⟨ZMod.val_injective p hx, ZMod.val_injective p hy⟩

-- Two distinct points lie on at most one non-vertical line.
theorem two_points {s b s' b' x y x' y' : ZMod p} (hne : (x, y) ≠ (x', y'))
    (h1 : s * x + b = y) (h2 : s' * x + b' = y) (h3 : s * x' + b = y') (h4 : s' * x' + b' = y') :
    (s, b) = (s', b') := by
  have hx : x ≠ x' := by
    rintro rfl
    exact hne (by rw [← h1, ← h3])
  have h5 : (s - s') * (x - x') = 0 := by linear_combination h1 - h2 - h3 + h4
  rcases mul_eq_zero.mp h5 with h | h
  · have hs : s = s' := sub_eq_zero.mp h
    subst hs
    have hb : b = b' := by linear_combination h1 - h2
    rw [hb]
  · exact absurd (sub_eq_zero.mp h) hx

-- A flag lies on its own line.
theorem onLine_self (f : Flag p) : onLine p f (line p f) := rfl

-- The relation orders the points, so a clique has distinct points; three flags with
-- `f < g < h` put the distinct points of `f` and `g` on the two distinct lines of `g` and `h`.
theorem no_triangle {f g h : Flag p} (hfg : irel p f g) (hfh : irel p f h) (hgh : irel p g h) :
    False := by
  obtain ⟨lfg, pfg, ofg⟩ := hfg
  obtain ⟨lfh, pfh, ofh⟩ := hfh
  obtain ⟨lgh, pgh, ogh⟩ := hgh
  apply lgh
  have hne : (f.1, yc p f) ≠ (g.1, yc p g) := by
    intro h
    have e : ptc p f = ptc p g := by
      unfold ptc; rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]
    omega
  have e := two_points p hne ofg (ofh) (onLine_self p g) ogh
  exact e

theorem ig_cliqueFree : (ig p).CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  have h1 := ((ig_adj p a b).mp (hS.isClique (by simp) (by simp) hab)).2
  have h2 := ((ig_adj p a c).mp (hS.isClique (by simp) (by simp) hac)).2
  have h3 := ((ig_adj p b c).mp (hS.isClique (by simp) (by simp) hbc)).2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · exact no_triangle p h1 h2 h3
  · exact no_triangle p h2 h1 h3
  · have := h1.2.1; have := h2.2.1; have := h3.2.1; omega
  · exact no_triangle p h2 h3 h1
  · exact no_triangle p h1 h3 h2
  · have := h1.2.1; have := h2.2.1; have := h3.2.1; omega
  · exact no_triangle p h3 h1 h2
  · exact no_triangle p h3 h2 h1

-- Independent sets have at most `|P| + |L| = 2p²` flags.
theorem ig_indep_card_le {I : Finset (Flag p)} (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ (ig p).Adj x y) :
    I.card ≤ p * p + p * p := by
  classical
  -- `top`: flags whose point is the largest of `I` on their line
  let top : Flag p → Prop := fun f => ∀ g ∈ I, line p g = line p f → ptc p g ≤ ptc p f
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) top
  have hA : (I.filter top).card ≤ p * p := by
    have hmaps : ∀ f ∈ I.filter top, line p f ∈ (Finset.univ : Finset (ZMod p × ZMod p)) :=
      fun _ _ => Finset.mem_univ _
    have hinj : Set.InjOn (line p) ↑(I.filter top) := by
      intro f hf g hg hfg
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hf hg
      have h1 := hf.2 g hg.1 hfg.symm
      have h2 := hg.2 f hf.1 hfg
      obtain ⟨hx, -⟩ := ptc_inj p (le_antisymm h2 h1)
      exact Prod.ext hx hfg
    calc (I.filter top).card ≤ (Finset.univ : Finset (ZMod p × ZMod p)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = p * p := by rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
  have hB : (I.filter (fun f => ¬ top f)).card ≤ p * p := by
    have hmaps : ∀ f ∈ I.filter (fun f => ¬ top f),
        (f.1, yc p f) ∈ (Finset.univ : Finset (ZMod p × ZMod p)) :=
      fun _ _ => Finset.mem_univ _
    have hinj : Set.InjOn (fun f : Flag p => (f.1, yc p f)) ↑(I.filter (fun f => ¬ top f)) := by
      intro f hf g hg hfg
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hf hg
      simp only [Prod.mk.injEq] at hfg
      by_contra hne
      have hl : line p f ≠ line p g := by
        intro h
        exact hne (Prod.ext hfg.1 h)
      -- some flag of `I` on the line of `f` has a larger point
      have : ∃ f' ∈ I, line p f' = line p f ∧ ptc p f < ptc p f' := by
        by_contra hcon
        push_neg at hcon
        exact hf.2 (fun g' hg' hl' => hcon g' hg' hl')
      obtain ⟨f', hf', hlf', hpf'⟩ := this
      apply hI g hg.1 f' hf'
      rw [ig_adj]
      refine ⟨fun h => ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [h] at hfg
        have e : ptc p f = ptc p f' := by unfold ptc; rw [hfg.1, hfg.2]
        omega
      · rw [hlf']; exact fun h => hl h.symm
      · have : ptc p g = ptc p f := by unfold ptc; rw [hfg.1, hfg.2]
        omega
      · rw [hlf']
        show (line p f).1 * g.1 + (line p f).2 = yc p g
        rw [← hfg.2, ← hfg.1]
        exact onLine_self p f
    calc (I.filter (fun f => ¬ top f)).card ≤ (Finset.univ : Finset (ZMod p × ZMod p)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = p * p := by rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
  omega

theorem good_inc : Good (p * (p * p)) (p * p + p * p) := by
  classical
  have hcard : Fintype.card (Flag p) = p * (p * p) := by
    simp only [Flag, Fintype.card_prod, ZMod.card]
  exact ⟨_, goodOn_comap ⟨ig_cliqueFree p, fun T hT => ig_indep_card_le p hT⟩
    (Fintype.equivFinOfCardEq hcard).symm.toEmbedding⟩

end Incidence

-- Lemmas.
theorem isqrtAux_le (f s n : ℕ) (h : s * s ≤ n) : isqrtAux f s n * isqrtAux f s n ≤ n := by
  induction f generalizing s with
  | zero => simpa [isqrtAux] using h
  | succ f ih =>
    simp only [isqrtAux]
    split_ifs with h1
    · exact ih _ h1
    · exact h

theorem isqrt_le (n : ℕ) : isqrt n * isqrt n ≤ n := isqrtAux_le n 0 n (by simp)

theorem primeBelowAux_le (f t : ℕ) : primeBelowAux f t ≤ t := by
  induction f generalizing t with
  | zero => simp [primeBelowAux]
  | succ f ih =>
    simp only [primeBelowAux]
    split_ifs
    · exact le_refl _
    · exact (ih (t - 1)).trans (Nat.sub_le _ _)

theorem primeBelowAux_prime (f t : ℕ) :
    primeBelowAux f t = 0 ∨ isPrime (primeBelowAux f t) = true := by
  induction f generalizing t with
  | zero => simp [primeBelowAux]
  | succ f ih =>
    simp only [primeBelowAux]
    split_ifs with h
    · exact Or.inr h
    · exact ih (t - 1)

theorem isPrime_prime {n : ℕ} (h : isPrime n = true) : Nat.Prime n := by
  unfold isPrime at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rw [Nat.prime_def_lt]
  refine ⟨h.1, fun m hm hdvd => ?_⟩
  rcases h.2 m hm with h2 | h2
  · interval_cases m
    all_goals first | rfl | exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by omega)
  · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h2

theorem inc_spec (m : ℕ) : inc m = 0 ∨
    ∃ q, Nat.Prime q ∧ inc m = q * (q * q) ∧ q * q + q * q ≤ m := by
  unfold inc
  rcases primeBelowAux_prime (isqrt (m / 2)) (isqrt (m / 2)) with h | h
  · left; unfold primeBelow; rw [h]
  · right
    refine ⟨primeBelow (isqrt (m / 2)), isPrime_prime h, rfl, ?_⟩
    have h1 : primeBelow (isqrt (m / 2)) ≤ isqrt (m / 2) := primeBelowAux_le _ _
    have h2 := isqrt_le (m / 2)
    have h3 : primeBelow (isqrt (m / 2)) * primeBelow (isqrt (m / 2)) ≤ isqrt (m / 2) * isqrt (m / 2) :=
      Nat.mul_le_mul h1 h1
    omega


theorem good_incm (m : ℕ) : Good (inc m) m := by
  rcases inc_spec m with h | ⟨q, hq, e, hle⟩
  · rw [h]
    exact good_mono_m (Nat.zero_le m) (by simpa using good_c5 0)
  · rw [e]
    haveI := Fact.mk hq
    exact good_mono_m hle (good_inc q)

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) :
    inc (k - 1) + 1 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  by_contra hcon
  obtain ⟨G, hG3, hGi⟩ := good_mono (show N ≤ inc (k - 1) by omega) (good_incm (k - 1))
  rcases h G with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact hG3 S hS
  · have hc := hGi T (SqueezeBench.Ramsey3.Lower.V005.indep_of_isClique_compl hT.isClique)
    rw [hT.card_eq] at hc
    omega

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f v :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey3.Lower.V006.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 1683) (by decide)
    (by decide +kernel)

end SqueezeBench.Ramsey3.Lower.V007
