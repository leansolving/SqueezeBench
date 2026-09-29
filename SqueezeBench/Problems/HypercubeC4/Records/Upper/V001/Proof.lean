import SqueezeBench.Problems.HypercubeC4.Records.Upper.V001.Def
import SqueezeBench.Problems.HypercubeC4.Records.Upper.V000.Proof

/-! Record V001 for HypercubeC4, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/HypercubeC4/Upper/V001.lean`. -/

namespace SqueezeBench.HypercubeC4.Upper.V001

open Finset SimpleGraph

-- Flipping distinct bits of a fixed word gives distinct words.
theorem flip_injective {n : ℕ} (x : Fin n → Bool) : Function.Injective (flip x) := by
  intro i j h
  by_contra hne
  have hi := congrFun h i
  simp [flip_apply, hne] at hi

-- The neighbours of `x` in the cube are exactly its `n` single-bit flips.
theorem neighborFinset_eq {n : ℕ} (x : Fin n → Bool) :
    (hypercube n).neighborFinset x = Finset.univ.image (flip x) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
  rw [hypercube_adj_iff]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩

theorem degree_eq {n : ℕ} (x : Fin n → Bool) : (hypercube n).degree x = n := by
  rw [SimpleGraph.degree, neighborFinset_eq, Finset.card_image_of_injective _ (flip_injective x),
    Finset.card_univ, Fintype.card_fin]

-- Handshake: the cube has `n · 2ⁿ⁻¹` edges.
theorem two_mul_card_edges (n : ℕ) : 2 * #(hypercube n).edgeFinset = n * 2 ^ n := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [Finset.sum_congr rfl (fun x _ => degree_eq x)]
  simp [Finset.card_univ, mul_comm]

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.HypercubeC4.f record := by
  intro n
  refine (f_le_card_edgeFinset_hypercube n).trans ?_
  show #(hypercube n).edgeFinset ≤ n * 2 ^ (n - 1)
  have h := two_mul_card_edges n
  have h2 : n * 2 ^ n = 2 * (n * 2 ^ (n - 1)) := by
    cases n with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring
  exact le_of_eq (Nat.eq_of_mul_eq_mul_left (by norm_num) (h.trans h2))

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.HypercubeC4.Upper.V000.record record := by
  intro n
  show n * 2 ^ (n - 1) ≤ (2 ^ n).choose 2
  rw [Nat.choose_two_right]
  cases n with
  | zero => simp
  | succ m =>
    have hp : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hlt : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
    have key : 2 ^ (m + 1) * (2 ^ (m + 1) - 1) / 2 = 2 ^ m * (2 ^ (m + 1) - 1) := by
      rw [hp, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [Nat.add_sub_cancel, key]
    calc (m + 1) * 2 ^ m ≤ (2 ^ (m + 1) - 1) * 2 ^ m :=
          Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hlt)
      _ = 2 ^ m * (2 ^ (m + 1) - 1) := Nat.mul_comm _ _

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.HypercubeC4.nMin SqueezeBench.HypercubeC4.Upper.V000.record record :=
  ⟨3, by decide, by decide⟩

end SqueezeBench.HypercubeC4.Upper.V001
