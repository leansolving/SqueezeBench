import SqueezeBench.Problems.ExC4.Records.Lower.V002.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V001.Proof

/-! Record V002 for ExC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V002.lean`. -/

namespace SqueezeBench.ExC4.Lower.V002

open Finset SimpleGraph SqueezeBench SqueezeBench.ExC4

-- Vertex of index `i` (taken mod `n`, which is the identity on the indices used below).
def vv (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

-- The friendship graph: vertex `0` is the hub, and `2k+1`, `2k+2` are partners.
def frGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (x.val = 0 ∨ y.val = 0 ∨ (x.val + 1) / 2 = (y.val + 1) / 2)
  symm := ⟨by rintro x y ⟨h, h'⟩; exact ⟨h.symm, by omega⟩⟩
  loopless := ⟨by rintro x ⟨h, -⟩; exact h rfl⟩

instance (n : ℕ) : DecidableRel (frGraph n).Adj :=
  fun x y =>
    inferInstanceAs (Decidable (x ≠ y ∧ (x.val = 0 ∨ y.val = 0 ∨ (x.val + 1) / 2 = (y.val + 1) / 2)))

-- Two vertices of the friendship graph share at most one neighbour: either the hub, or,
-- inside a triangle, the third vertex of that triangle.
theorem frGraph_free (n : ℕ) : NoTwoCommonNeighbours (frGraph n) := by
  rintro x y u v hxy huv ⟨hxu0, hxu⟩ ⟨hyu0, hyu⟩ ⟨hxv0, hxv⟩ ⟨hyv0, hyv⟩
  have h1 : x.val ≠ u.val := fun h => hxu0 (Fin.ext h)
  have h2 : y.val ≠ u.val := fun h => hyu0 (Fin.ext h)
  have h3 : x.val ≠ v.val := fun h => hxv0 (Fin.ext h)
  have h4 : y.val ≠ v.val := fun h => hyv0 (Fin.ext h)
  have h5 : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have h6 : u.val ≠ v.val := fun h => huv (Fin.ext h)
  omega

theorem fr_card (n : ℕ) (hn : 0 < n) :
    (n - 1) + (n - 1) / 2 ≤ #(frGraph n).edgeFinset := by
  have hlt : ∀ i ∈ Finset.range ((n - 1) / 2), 2 * i + 2 < n := by
    intro i hi
    rw [Finset.mem_range] at hi
    omega
  have hval1 : ∀ i ∈ Finset.range ((n - 1) / 2), (vv n hn (2 * i + 1)).val = 2 * i + 1 :=
    fun i hi => Nat.mod_eq_of_lt (by have := hlt i hi; omega)
  have hval2 : ∀ i ∈ Finset.range ((n - 1) / 2), (vv n hn (2 * i + 2)).val = 2 * i + 2 :=
    fun i hi => Nat.mod_eq_of_lt (hlt i hi)
  have hcv : (vv n hn 0).val = 0 := Nat.zero_mod n
  -- the star at the hub
  have hcardA :
      #((univ.erase (vv n hn 0)).image fun v => s(vv n hn 0, v)) = n - 1 := by
    rw [Finset.card_image_of_injOn (fun a _ b _ h => Sym2.congr_right.mp h),
      Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- one further edge inside each triangle
  have hcardB :
      #((Finset.range ((n - 1) / 2)).image
        fun i => s(vv n hn (2 * i + 1), vv n hn (2 * i + 2))) = (n - 1) / 2 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    have hi' : i ∈ Finset.range ((n - 1) / 2) := by simpa using hi
    have hj' : j ∈ Finset.range ((n - 1) / 2) := by simpa using hj
    have e1 := hval1 i hi'
    have e2 := hval2 i hi'
    have e3 := hval1 j hj'
    have e4 := hval2 j hj'
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have a1 := congrArg Fin.val h1
      rw [e1, e3] at a1
      omega
    · have a1 := congrArg Fin.val h1
      rw [e1, e4] at a1
      omega
  have hdisj :
      Disjoint ((univ.erase (vv n hn 0)).image fun v => s(vv n hn 0, v))
        ((Finset.range ((n - 1) / 2)).image
          fun i => s(vv n hn (2 * i + 1), vv n hn (2 * i + 2))) := by
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [Finset.mem_image, Finset.mem_erase] at heA heB
    obtain ⟨w, -, rfl⟩ := heA
    obtain ⟨i, hi, hie⟩ := heB
    have hi' : i ∈ Finset.range ((n - 1) / 2) := by simpa using hi
    have e1 := hval1 i hi'
    have e2 := hval2 i hi'
    rcases Sym2.eq_iff.mp hie with ⟨h1, -⟩ | ⟨-, h2⟩
    · have a1 := congrArg Fin.val h1
      rw [e1, hcv] at a1
      omega
    · have a1 := congrArg Fin.val h2
      rw [e2, hcv] at a1
      omega
  have hsub :
      ((univ.erase (vv n hn 0)).image fun v => s(vv n hn 0, v)) ∪
        ((Finset.range ((n - 1) / 2)).image
          fun i => s(vv n hn (2 * i + 1), vv n hn (2 * i + 2))) ⊆ (frGraph n).edgeFinset := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · simp only [Finset.mem_image, Finset.mem_erase] at he
      obtain ⟨w, ⟨hw, -⟩, rfl⟩ := he
      simp only [mem_edgeFinset, mem_edgeSet]
      exact ⟨fun h => hw h.symm, Or.inl hcv⟩
    · simp only [Finset.mem_image] at he
      obtain ⟨i, hi, rfl⟩ := he
      have e1 := hval1 i hi
      have e2 := hval2 i hi
      simp only [mem_edgeFinset, mem_edgeSet]
      refine ⟨fun h => ?_, Or.inr (Or.inr (by omega))⟩
      have := congrArg Fin.val h
      omega
  calc (n - 1) + (n - 1) / 2
      = #(((univ.erase (vv n hn 0)).image fun v => s(vv n hn 0, v)) ∪
        ((Finset.range ((n - 1) / 2)).image
          fun i => s(vv n hn (2 * i + 1), vv n hn (2 * i + 2)))) := by
        rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB]
    _ ≤ #(frGraph n).edgeFinset := Finset.card_le_card hsub

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · exact le_trans (fr_card n hn) (le_f_of_noTwoCommonNeighbours hn (frGraph_free n))

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V001.record record :=
  fun _ => Nat.le_add_right _ _

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V001.record record :=
  ⟨3, by decide, by decide⟩

end SqueezeBench.ExC4.Lower.V002
