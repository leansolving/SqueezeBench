import SqueezeBench.Problems.HypercubeC4.Records.Lower.V002.Def
import SqueezeBench.Problems.HypercubeC4.Records.Lower.V001.Proof

/-! Record V002 for HypercubeC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Lower/V002.lean`. -/

namespace SqueezeBench.HypercubeC4.Lower.V002

open Finset SimpleGraph

-- Flips in two directions commute.
theorem flip_comm {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    HypercubeC4.flip (HypercubeC4.flip x i) j = HypercubeC4.flip (HypercubeC4.flip x j) i := by
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · funext m
    by_cases hi : m = i <;> by_cases hj : m = j <;>
      simp [HypercubeC4.flip_apply, hi, hj, hne, Ne.symm hne]

-- V001's parity graph, with every edge in direction `l` put back.
def Q (n : ℕ) (l : Fin n) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1 ∧ (x l ≠ y l ∨ (V001.wt x + V001.wt y) % 4 = 1)
  symm := ⟨fun x y h => ⟨by rw [hammingDist_comm]; exact h.1,
    h.2.imp (fun hh => Ne.symm hh) (fun hh => by omega)⟩⟩
  loopless := ⟨fun x h => absurd h.1 (by simp)⟩

instance decQ (n : ℕ) (l : Fin n) : DecidableRel (Q n l).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1 ∧
    (x l ≠ y l ∨ (V001.wt x + V001.wt y) % 4 = 1)))

theorem Q_le (n : ℕ) (l : Fin n) : Q n l ≤ HypercubeC4.hypercube n := fun _ _ h => h.1

-- An edge is kept when it runs in direction `l`, or when V001's parity rule keeps it.
theorem adjQ {n : ℕ} (l : Fin n) (x : Fin n → Bool) (i : Fin n) :
    (Q n l).Adj x (HypercubeC4.flip x i) ↔ (i = l ∨ V001.keep x i) := by
  have hd : hammingDist x (HypercubeC4.flip x i) = 1 :=
    HypercubeC4.hypercube_adj.mp (HypercubeC4.hypercube_adj_iff.mpr ⟨i, rfl⟩)
  have hl : (x l ≠ HypercubeC4.flip x i l) ↔ i = l := by
    by_cases h : i = l
    · subst h
      simp only [HypercubeC4.flip_apply, iff_true]
      cases hx : x i <;> simp
    · simp [HypercubeC4.flip_apply, Ne.symm h, h]
  constructor
  · rintro ⟨-, h⟩
    exact h.imp (fun hh => hl.mp hh) (fun hh => hh)
  · intro h
    exact ⟨hd, h.imp (fun hh => hl.mpr hh) (fun hh => hh)⟩

-- No square survives: a square either avoids direction `l`, and then V001's argument applies, or
-- it has two parallel edges in a direction other than `l`, exactly one of which V001 keeps.
theorem not_hasSquareQ {n : ℕ} (l : Fin n) : ¬ HypercubeC4.HasSquare (Q n l) := by
  rintro ⟨x, i, j, hij, h1, h2, h3, h4⟩
  have k1 := (adjQ l x i).mp h1
  have k2 := (adjQ l x j).mp h2
  have k3 := (adjQ l (HypercubeC4.flip x i) j).mp h3
  have k4 := (adjQ l (HypercubeC4.flip x j) i).mp (by rw [← flip_comm]; exact h4)
  rcases eq_or_ne i l with rfl | hil
  · have hjl : j ≠ i := Ne.symm hij
    have a2 : V001.keep x j := k2.resolve_left hij.symm
    have a3 : V001.keep (HypercubeC4.flip x i) j := k3.resolve_left hij.symm
    exact (V001.keep_flip x hjl.symm).mp a3 a2
  · rcases eq_or_ne j l with rfl | hjl
    · have a1 : V001.keep x i := k1.resolve_left hil
      have a4 : V001.keep (HypercubeC4.flip x j) i := k4.resolve_left hil
      exact (V001.keep_flip x (Ne.symm hij)).mp a4 a1
    · refine V001.not_hasSquare n ⟨x, i, j, hij, (V001.adj_flip x i).mpr (k1.resolve_left hil),
        (V001.adj_flip x j).mpr (k2.resolve_left hjl),
        (V001.adj_flip (HypercubeC4.flip x i) j).mpr (k3.resolve_left hjl), ?_⟩
      rw [flip_comm]
      exact (V001.adj_flip (HypercubeC4.flip x j) i).mpr (k4.resolve_left hil)

theorem degreeQ {n : ℕ} (l : Fin n) (x : Fin n → Bool) :
    (Q n l).degree x = (Finset.univ.filter (fun i : Fin n => i = l ∨ V001.keep x i)).card := by
  show ((Q n l).neighborFinset x).card = _
  refine (Finset.card_bij (fun i _ => HypercubeC4.flip x i) ?_ ?_ ?_).symm
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ((adjQ l x a).mpr ha.2)
  · intro a _ b _ hab
    exact V001.flip_inj x hab
  · intro y hy
    have hadj : (Q n l).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    obtain ⟨i, rfl⟩ := HypercubeC4.hypercube_adj_iff.mp (Q_le n l hadj)
    exact ⟨i, by simp [Finset.mem_filter, (adjQ l x i).mp hadj], rfl⟩

theorem sum_degreeQ {n : ℕ} (hn : 2 ≤ n) (l : Fin n) :
    ∑ x : Fin n → Bool, (Q n l).degree x = 2 ^ n + (n - 1) * 2 ^ (n - 1) := by
  have h1 : ∀ x : Fin n → Bool,
      (Q n l).degree x = ∑ i : Fin n, if i = l ∨ V001.keep x i then 1 else 0 := by
    intro x
    rw [degreeQ, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
  have hl : (∑ x : Fin n → Bool, if l = l ∨ V001.keep x l then (1 : ℕ) else 0) = 2 ^ n := by
    simp [Finset.card_univ]
  have he : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase l,
      (∑ x : Fin n → Bool, if i = l ∨ V001.keep x i then (1 : ℕ) else 0) = 2 ^ (n - 1) := by
    intro i hi
    have hne : i ≠ l := Finset.ne_of_mem_erase hi
    simp only [hne, false_or]
    rw [← Finset.card_filter]
    exact V001.card_keep hn i
  rw [hl, Finset.sum_congr rfl he, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

theorem card_edgesQ {m : ℕ} (l : Fin (m + 2)) :
    ((Q (m + 2) l).edgeFinset).card = (m + 3) * 2 ^ m := by
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (Q (m + 2) l)
  rw [sum_degreeQ (by omega) l] at h
  have e1 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  have e2 : (2 : ℕ) ^ (m + 2 - 1) = 2 * 2 ^ m := by
    rw [show m + 2 - 1 = m + 1 from rfl, pow_succ]; ring
  rw [e1, e2, show m + 2 - 1 = m + 1 from rfl] at h
  have h3 : 2 * ((m + 3) * 2 ^ m) = 2 * (((Q (m + 2) l).edgeFinset).card) := by
    rw [← h]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h3).symm

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.HypercubeC4.f record := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Nat.zero_le _
    · have hr : record 1 = 1 := by norm_num [record]
      rw [hr]
      exact V001.one_le_f_one
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hr : record (m + 2) = (m + 3) * 2 ^ m := by
      simp only [record, if_neg (by omega : ¬ m + 2 < 2), show m + 2 - 2 = m from rfl]
      try ring
    rw [hr, ← card_edgesQ (l := (⟨0, by omega⟩ : Fin (m + 2)))]
    exact HypercubeC4.le_f_of_not_hasSquare (by rw [HypercubeC4.nMin_eq]; omega)
      (Q_le _ _) (not_hasSquareQ _)

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.HypercubeC4.Lower.V001.record record := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Nat.le_refl _
    · norm_num [record, V001.record]
  · show V001.record n ≤ if n < 2 then n else (n + 1) * 2 ^ (n - 2)
    rw [if_neg (by omega)]
    show n * 2 ^ (n - 2) ≤ (n + 1) * 2 ^ (n - 2)
    exact Nat.mul_le_mul_right _ (by omega)

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Lower.V001.record record :=
  ⟨6, by decide, by decide⟩

end SqueezeBench.HypercubeC4.Lower.V002
