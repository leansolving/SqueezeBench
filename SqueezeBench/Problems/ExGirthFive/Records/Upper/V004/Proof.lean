import SqueezeBench.Problems.ExGirthFive.Records.Upper.V004.Def
import SqueezeBench.Problems.ExGirthFive.Records.Upper.V003.Proof

/-! Record V004 for ExGirthFive, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Upper/V004.lean`.

V003 used the per-vertex count `∑_{u ~ x} d(u) ≤ n - 1` only through its consequence on the
minimum degree, and so pulled a single vertex out of the chord sum. Here the whole
neighbourhood is used. If some vertex `v` has degree at least `q + 1`, its neighbours have
degrees summing to at most `n - 1`, so their total shortfall below `q` is at least
`q(q+1) - (n-1)`. The chord of `x ↦ x²` at `q` is slack by `(q-d)(q+1-d) ≥ 2(q-d)` at a vertex
of degree `d`, so the chord sum gains twice that shortfall — a gain of order `√n`, against the
constant gain of V003. -/

namespace SqueezeBench.ExGirthFive.Upper.V004

open Finset SimpleGraph

-- The chord of `x ↦ x²` at `q`, with its slack `(q-d)(q+1-d) ≥ 2(q-d)` made explicit.
theorem chordDef (d q : ℕ) : (2 * q + 1) * d + 2 * q ≤ d * d + q * (q + 1) + 2 * d := by
  rcases Nat.le_total d q with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, q = d + e := ⟨q - d, by omega⟩
    nlinarith [Nat.le_mul_of_pos_left e (Nat.zero_lt_one), sq_nonneg e]
  · obtain ⟨e, rfl⟩ : ∃ e, d = q + e := ⟨d - q, by omega⟩
    nlinarith

theorem bnd_valid (q : ℕ) :
    SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f (fun n => bnd n q) := by
  intro n
  match n with
  | 0 => exact le_trans (by simpa using SqueezeBench.ExGirthFive.f_le_choose_two 0) (Nat.zero_le _)
  | (k + 1) =>
    refine SqueezeBench.ExGirthFive.f_le_of_forall_cliqueFree_noTwoCommonNeighbours
      (Nat.succ_le_succ (Nat.zero_le k)) fun G _ h3 h4 => ?_
    classical
    simp only [bnd, Nat.add_sub_cancel]
    by_cases hall : ∀ u : Fin (k + 1), G.degree u ≤ q
    · refine le_trans ?_ (le_max_left _ _)
      have h2m : 2 * #G.edgeFinset ≤ (k + 1) * q := by
        rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
        calc ∑ u : Fin (k + 1), G.degree u ≤ ∑ _u : Fin (k + 1), q :=
              Finset.sum_le_sum fun u _ => hall u
          _ = (k + 1) * q := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      set A := (k + 1) * q with hA
      omega
    · refine le_trans ?_ (le_max_right _ _)
      simp only [not_forall, Nat.not_le] at hall
      obtain ⟨v0, hv0⟩ := hall
      set N := G.neighborFinset v0 with hN
      set X := q * (q + 1) with hX
      set SA := ∑ u ∈ N, G.degree u with hSA
      set SB := ∑ u ∈ Nᶜ, G.degree u with hSB
      set QA := ∑ u ∈ N, G.degree u * G.degree u with hQA
      set QB := ∑ u ∈ Nᶜ, G.degree u * G.degree u with hQB
      have hcard : #N = G.degree v0 := card_neighborFinset_eq_degree G v0
      -- the chord on the neighbourhood, with the slack kept
      have h1 : (2 * q + 1) * SA + 2 * q * G.degree v0 ≤ QA + G.degree v0 * X + 2 * SA := by
        have := Finset.sum_le_sum (f := fun u => (2 * q + 1) * G.degree u + 2 * q)
          (g := fun u => G.degree u * G.degree u + X + 2 * G.degree u)
          (s := N) fun u _ => chordDef (G.degree u) q
        simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
          hcard] at this
        calc (2 * q + 1) * SA + 2 * q * G.degree v0
            = (2 * q + 1) * SA + G.degree v0 * (2 * q) := by rw [hSA]; ring
          _ ≤ (QA + G.degree v0 * X) + 2 * SA := this
          _ = QA + G.degree v0 * X + 2 * SA := by ring
      -- the plain chord elsewhere
      have h2 : (2 * q + 1) * SB ≤ QB + #(Nᶜ : Finset (Fin (k + 1))) * X := by
        have := Finset.sum_le_sum (f := fun u => (2 * q + 1) * G.degree u)
          (g := fun u => G.degree u * G.degree u + X)
          (s := (Nᶜ : Finset (Fin (k + 1)))) fun u _ => by nlinarith [chordDef (G.degree u) q]
        simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
          hSB, hQB] using this
      have hcc : G.degree v0 + #(Nᶜ : Finset (Fin (k + 1))) = k + 1 := by
        rw [← hcard]
        simpa using Finset.card_add_card_compl N
      have hdeg : SA + SB = 2 * #G.edgeFinset := by
        rw [hSA, hSB, Finset.sum_add_sum_compl, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      have hSS : QA + QB ≤ (k + 1) * k := by
        have h := V001.sum_sq_degree_le G h3 h4
        have hrw : ∑ w : Fin (k + 1), G.degree w ^ 2 = QA + QB := by
          rw [hQA, hQB, ← Finset.sum_add_sum_compl N]
          simp [pow_two]
        rw [hrw] at h
        calc QA + QB ≤ (k + 1) * (k + 1) - (k + 1) := h
          _ = (k + 1) * k := by rw [Nat.mul_succ, Nat.add_sub_cancel]
      have hSAle : SA ≤ k := by
        have := V003.nbr_sum_le G h3 h4 v0
        rw [Nat.add_sub_cancel] at this
        exact this
      have hq1 : 2 * q * (q + 1) ≤ 2 * q * G.degree v0 :=
        Nat.mul_le_mul_left _ hv0
      have key : (2 * q + 1) * (2 * #G.edgeFinset) + 2 * X
          ≤ (k + 1) * k + (k + 1) * X + 2 * k := by
        have hsum : (2 * q + 1) * SA + (2 * q + 1) * SB + 2 * q * G.degree v0
            ≤ (QA + QB) + (G.degree v0 + #(Nᶜ : Finset (Fin (k + 1)))) * X + 2 * SA := by
          calc (2 * q + 1) * SA + (2 * q + 1) * SB + 2 * q * G.degree v0
              = ((2 * q + 1) * SA + 2 * q * G.degree v0) + (2 * q + 1) * SB := by ring
            _ ≤ (QA + G.degree v0 * X + 2 * SA) + (QB + #(Nᶜ : Finset (Fin (k + 1))) * X) :=
                Nat.add_le_add h1 h2
            _ = (QA + QB) + (G.degree v0 + #(Nᶜ : Finset (Fin (k + 1)))) * X + 2 * SA := by ring
        rw [hcc] at hsum
        have hX2 : 2 * X = 2 * q * (q + 1) := by rw [hX]; ring
        calc (2 * q + 1) * (2 * #G.edgeFinset) + 2 * X
            = (2 * q + 1) * SA + (2 * q + 1) * SB + 2 * q * (q + 1) := by
              rw [← hdeg, hX2]; ring
          _ ≤ (2 * q + 1) * SA + (2 * q + 1) * SB + 2 * q * G.degree v0 :=
              Nat.add_le_add_left hq1 _
          _ ≤ (QA + QB) + (k + 1) * X + 2 * SA := hsum
          _ ≤ (k + 1) * k + (k + 1) * X + 2 * k :=
              Nat.add_le_add (Nat.add_le_add_right hSS _) (Nat.mul_le_mul_left 2 hSAle)
      refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
      have hmul : #G.edgeFinset * (2 * (2 * q + 1)) = (2 * q + 1) * (2 * #G.edgeFinset) := by ring
      rw [hmul]
      set E := (2 * q + 1) * (2 * #G.edgeFinset) with hE
      set Y := (k + 1) * k with hY
      set Z := (k + 1) * X with hZ
      omega

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f v := by
  intro n
  simp only [v]
  exact le_min (bnd_valid _ n) (le_min (bnd_valid _ n) (bnd_valid _ n))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.minWith_valid SqueezeBench.ExGirthFive.Upper.V003.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.ExGirthFive.Upper.V003.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.ExGirthFive.nMin SqueezeBench.ExGirthFive.Upper.V003.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 19) (by decide)
    (by decide +kernel)

end SqueezeBench.ExGirthFive.Upper.V004
