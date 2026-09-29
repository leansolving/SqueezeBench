import SqueezeBench.Problems.ExGirthFive.Records.Lower.V001.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V000.Proof

/-! Record V001 for ExGirthFive, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V001.lean`. -/

namespace SqueezeBench.ExGirthFive.Lower.V001

open Finset SimpleGraph SqueezeBench SqueezeBench.ExGirthFive

-- The star with centre the vertex of index `0`.
def starGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (x.val = 0 ∨ y.val = 0)
  symm := ⟨by rintro x y ⟨h, h'⟩; exact ⟨h.symm, h'.symm⟩⟩
  loopless := ⟨by rintro x ⟨h, -⟩; exact h rfl⟩

instance (n : ℕ) : DecidableRel (starGraph n).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (x.val = 0 ∨ y.val = 0)))

-- A triangle would need two distinct non-central vertices to be adjacent.
theorem starGraph_cliqueFree (n : ℕ) : (starGraph n).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  obtain ⟨hab1, hab2⟩ := hab
  obtain ⟨hac1, hac2⟩ := hac
  obtain ⟨hbc1, hbc2⟩ := hbc
  have h1 : a.val ≠ b.val := fun h => hab1 (Fin.ext h)
  have h2 : a.val ≠ c.val := fun h => hac1 (Fin.ext h)
  have h3 : b.val ≠ c.val := fun h => hbc1 (Fin.ext h)
  omega

-- Two distinct vertices of a star have at most the centre as a common neighbour.
theorem starGraph_noTwo (n : ℕ) : NoTwoCommonNeighbours (starGraph n) := by
  rintro x y u v hxy huv ⟨hxu0, hxu⟩ ⟨hyu0, hyu⟩ ⟨hxv0, hxv⟩ ⟨hyv0, hyv⟩
  have h1 : x.val ≠ u.val := fun h => hxu0 (Fin.ext h)
  have h2 : y.val ≠ u.val := fun h => hyu0 (Fin.ext h)
  have h3 : x.val ≠ v.val := fun h => hxv0 (Fin.ext h)
  have h4 : y.val ≠ v.val := fun h => hyv0 (Fin.ext h)
  have h5 : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have h6 : u.val ≠ v.val := fun h => huv (Fin.ext h)
  omega

-- The `n - 1` edges from the centre are distinct edges of the star.
theorem star_card (n : ℕ) (hn : 1 ≤ n) : n - 1 ≤ #(starGraph n).edgeFinset := by
  have hc : (0 : ℕ) < n := hn
  have hsub : ((univ.erase (⟨0, hc⟩ : Fin n)).image fun v => s((⟨0, hc⟩ : Fin n), v))
      ⊆ (starGraph n).edgeFinset := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_erase] at he
    obtain ⟨v, ⟨hv, -⟩, rfl⟩ := he
    simp only [mem_edgeFinset, mem_edgeSet]
    exact ⟨fun h => hv h.symm, Or.inl rfl⟩
  have hinj : Set.InjOn (fun v : Fin n => s((⟨0, hc⟩ : Fin n), v))
      ↑(univ.erase (⟨0, hc⟩ : Fin n)) := by
    intro a _ b _ h
    exact Sym2.congr_right.mp h
  have hcard : #((univ.erase (⟨0, hc⟩ : Fin n)).image fun v => s((⟨0, hc⟩ : Fin n), v)) = n - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  exact hcard ▸ Finset.card_le_card hsub

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · exact le_trans (star_card n hn)
      (le_f_of_cliqueFree_of_noTwoCommonNeighbours hn (starGraph_cliqueFree n) (starGraph_noTwo n))

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V000.record record :=
  fun _ => Nat.zero_le _

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V000.record record :=
  ⟨2, by decide, by decide⟩

end SqueezeBench.ExGirthFive.Lower.V001
