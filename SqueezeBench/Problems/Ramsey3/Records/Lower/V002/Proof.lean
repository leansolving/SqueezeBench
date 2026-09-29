import SqueezeBench.Problems.Ramsey3.Records.Lower.V002.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V001.Proof

-- Record V002 for Ramsey3, lower direction, by baseline claude-opus-5.
--
-- Witness graph: the circulant on `Z_{3t+1}` joining two vertices when their cyclic distance
-- is more than `t`. It is triangle-free: for `a < b < c` the three distances force
-- `t < b - a < 2t+1`, `t < c - b < 2t+1` and `t < c - a < 2t+1`, and the first two give
-- `c - a > 2t`.
--
-- An independent set has all pairwise distances at most `t`. Measuring from its smallest
-- element `a`, every element sits at `x - a ≤ t` or at `x - a ≥ 2t+1`, and any two of those
-- two kinds are at least `2t+1` apart. So `x ↦ (x - a` or `x - a - 2t)` is injective into
-- `range (t+1)`, and the independence number is at most `t+1`.
--
-- Taking `t = k-2` gives independence number `k-1` on `3(k-2)+1 = 3k-5` vertices, so
-- `R(3,k) ≥ 3k - 4`. This beats `V001`'s `⌊5(k-1)/2⌋+1` at every `k ≥ 6`, and is folded in
-- with `maxWith` because `V001` is larger at `k = 2, 3`.

namespace SqueezeBench.Ramsey3.Lower.V002

open SqueezeBench SimpleGraph

-- Cyclic distance on `Z_n`, written without `%` so that `omega` can see it.
def sep (n x y : ℕ) : ℕ := min (max x y - min x y) (n - (max x y - min x y))

theorem sep_self (n x : ℕ) : sep n x x = 0 := by unfold sep; omega

-- The circulant, restricted to the first `N` vertices of `Z_{3t+1}`.
def circ (t N : ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun x y : Fin N => t < sep (3 * t + 1) (x : ℕ) (y : ℕ))

theorem circ_adj {t N : ℕ} (x y : Fin N) :
    (circ t N).Adj x y ↔ t < sep (3 * t + 1) (x : ℕ) (y : ℕ) := by
  unfold circ
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · unfold sep at h ⊢; omega
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [sep_self] at h
    omega

theorem circ_cliqueFree_three {t N : ℕ} (hN : N ≤ 3 * t + 1) : (circ t N).CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  have h1 := (circ_adj _ _).mp (hS.isClique (by simp) (by simp) hab)
  have h2 := (circ_adj _ _).mp (hS.isClique (by simp) (by simp) hac)
  have h3 := (circ_adj _ _).mp (hS.isClique (by simp) (by simp) hbc)
  have ha : (a : ℕ) < N := a.isLt
  have hb : (b : ℕ) < N := b.isLt
  have hc : (c : ℕ) < N := c.isLt
  unfold sep at h1 h2 h3
  omega

-- An independent set has at most `t + 1` vertices.
theorem indep_card_le {t N : ℕ} (hN : N ≤ 3 * t + 1) {T : Finset (Fin N)}
    (hT : ∀ x ∈ T, ∀ y ∈ T, sep (3 * t + 1) (x : ℕ) (y : ℕ) ≤ t) : T.card ≤ t + 1 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  set I := T.image (fun x : Fin N => (x : ℕ)) with hI
  have hIne : I.Nonempty := hne.image _
  set a := I.min' hIne with hadef
  obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp (I.min'_mem hIne)
  have hz3 : (z : ℕ) = a := hza
  have hale : ∀ x ∈ T, a ≤ (x : ℕ) := fun x hx => I.min'_le _ (Finset.mem_image_of_mem _ hx)
  -- every vertex is near `a` on one side or the other
  have hnear : ∀ x ∈ T, (x : ℕ) - a ≤ t ∨ 2 * t + 1 ≤ (x : ℕ) - a := by
    intro x hx
    have h1 := hT z hz x hx
    have h2 := hale x hx
    have h3 : (x : ℕ) < N := x.isLt
    rw [hz3] at h1
    unfold sep at h1
    omega
  have hmaps : ∀ x ∈ T,
      (if (x : ℕ) - a ≤ t then (x : ℕ) - a else (x : ℕ) - a - 2 * t) ∈ Finset.range (t + 1) := by
    intro x hx
    have h1 := hnear x hx
    have h2 := hale x hx
    have h3 : (x : ℕ) < N := x.isLt
    rw [Finset.mem_range]
    split_ifs with hc <;> omega
  have hinj : Set.InjOn
      (fun x : Fin N => if (x : ℕ) - a ≤ t then (x : ℕ) - a else (x : ℕ) - a - 2 * t) ↑T := by
    intro x hx y hy hxy
    simp only at hxy
    have hx1 := hale x hx
    have hy1 := hale y hy
    have hx2 := hnear x hx
    have hy2 := hnear y hy
    have hx3 : (x : ℕ) < N := x.isLt
    have hy3 : (y : ℕ) < N := y.isLt
    have hs := hT x hx y hy
    unfold sep at hs
    split_ifs at hxy with hcx hcy hcy <;> exact Fin.ext (by omega)
  calc T.card ≤ (Finset.range (t + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = t + 1 := Finset.card_range _

theorem le_of_forces {k N : ℕ} (hk : nMin ≤ k) (h : Ramsey.Forces N 3 k) : 3 * k - 4 ≤ N := by
  have hk2 : (2 : ℕ) ≤ k := hk
  by_contra hcon
  have hN : N ≤ 3 * (k - 2) + 1 := by omega
  rcases h (circ (k - 2) N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact circ_cliqueFree_three hN S hS
  · have hind : ∀ x ∈ T, ∀ y ∈ T, sep (3 * (k - 2) + 1) (x : ℕ) (y : ℕ) ≤ (k - 2) := by
      intro x hx y hy
      rcases eq_or_ne x y with rfl | hne
      · rw [sep_self]; exact Nat.zero_le _
      · have hc := hT.isClique hx hy hne
        rw [compl_adj] at hc
        have := hc.2
        rw [circ_adj] at this
        omega
    have hcard := indep_card_le (t := k - 2) (N := N) hN hind
    rw [hT.card_eq] at hcard
    omega

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f v :=
  pin_lowerBoundHolds fun _ hk => le_f hk fun _ h => le_of_forces hk h

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey3.f record :=
  maxWith_valid SqueezeBench.Ramsey3.Lower.V001.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey3.Lower.V001.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Lower.V001.record record :=
  maxWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 9) (by decide) (by decide)

end SqueezeBench.Ramsey3.Lower.V002
