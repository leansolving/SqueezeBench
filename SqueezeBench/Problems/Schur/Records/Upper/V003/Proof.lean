import SqueezeBench.Problems.Schur.Records.Upper.V003.Def
import SqueezeBench.Problems.Schur.Records.Upper.V002.Proof

/-! Record V003 for Schur, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Schur/Upper/V003.lean`. -/

namespace SqueezeBench.Schur.Upper.V003

open SqueezeBench Finset SqueezeBench.Schur

-- Let `a = ram (i+1) - 1 = 2s+1`, odd, and `N = 2m` with `m = (i+2) * s + 1`. At the
-- midpoint vertex `m` of the gap colouring of `{0, …, N}` the colour-`c` neighbourhood is
-- `{m - x, m + x : x ∈ A_c ∩ [1,m]}`, of even size `2 * |A_c ∩ [1,m]| ≤ a`, so
-- `|A_c ∩ [1,m]| ≤ s`. Summing over the `i+2` colours gives `m ≤ (i+2) * s`, false.
theorem forces_half {i s : ℕ} (hram : V001.ram (i + 1) = 2 * s + 2) :
    Forces (i + 2) (2 * ((i + 2) * s + 1)) := by
  classical
  set m := (i + 2) * s + 1 with hm
  set N := 2 * m with hN
  intro col
  by_contra hno
  have SF : ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → z ≤ N → x + y = z →
      col x = col y → col y = col z → False := by
    intro x y z hx hy hz hxy h1 h2
    exact hno ⟨x, by rw [Finset.mem_Icc]; omega, y, by rw [Finset.mem_Icc]; omega,
      z, by rw [Finset.mem_Icc]; omega, hxy, h1, h2⟩
  -- the colour-`c` neighbourhood of the midpoint vertex `m`
  have hW : ∀ c : Fin (i + 2),
      2 * ((Finset.Icc 1 m).filter (fun x => col x = c)).card ≤ 2 * s + 1 := by
    intro c
    set P := (Finset.Icc 1 m).filter (fun x => col x = c) with hP
    have hPb : ∀ x ∈ P, 1 ≤ x ∧ x ≤ m ∧ col x = c := by
      intro x hx
      rw [hP, Finset.mem_filter, Finset.mem_Icc] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    set W := P.image (fun x => m - x) ∪ P.image (fun x => m + x) with hWdef
    have hdisj : Disjoint (P.image (fun x => m - x)) (P.image (fun x => m + x)) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hy1
      obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hy2
      have b1 := hPb x1 hx1
      have b2 := hPb x2 hx2
      omega
    have hinj1 : (P.image (fun x => m - x)).card = P.card := by
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      have b1 := hPb x (Finset.mem_coe.mp hx)
      have b2 := hPb y (Finset.mem_coe.mp hy)
      have hxy' : m - x = m - y := hxy
      omega
    have hinj2 : (P.image (fun x => m + x)).card = P.card := by
      refine Finset.card_image_of_injOn ?_
      intro x _ y _ hxy
      have hxy' : m + x = m + y := hxy
      omega
    have hcardW : W.card = 2 * P.card := by
      rw [hWdef, Finset.card_union_of_disjoint hdisj, hinj1, hinj2]; ring
    have hWN : ∀ y ∈ W, y ≤ N := by
      intro y hy
      rw [hWdef, Finset.mem_union] at hy
      rcases hy with h | h
      · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
        have b := hPb x hx
        omega
      · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
        have b := hPb x hx
        omega
    have hgapW : ∀ p ∈ W, ∀ q ∈ W, p < q → col (q - p) ≠ c := by
      intro p hp q hq hpq hcc
      rw [hWdef, Finset.mem_union] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPb x1 hx1
        have b2 := hPb x2 hx2
        have hcc' : col (x1 - x2) = c := by
          rw [show x1 - x2 = q - p from by omega]; exact hcc
        exact SF x2 (x1 - x2) x1 (by omega) (by omega) (by omega) (by omega)
          (by rw [b2.2.2, hcc']) (by rw [hcc', b1.2.2])
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPb x1 hx1
        have b2 := hPb x2 hx2
        have hcc' : col (x1 + x2) = c := by
          rw [show x1 + x2 = q - p from by omega]; exact hcc
        exact SF x1 x2 (x1 + x2) (by omega) (by omega) (by omega) (by omega)
          (by rw [b1.2.2, b2.2.2]) (by rw [b2.2.2, hcc'])
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPb x1 hx1
        have b2 := hPb x2 hx2
        omega
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPb x1 hx1
        have b2 := hPb x2 hx2
        have hcc' : col (x2 - x1) = c := by
          rw [show x2 - x1 = q - p from by omega]; exact hcc
        exact SF x1 (x2 - x1) x2 (by omega) (by omega) (by omega) (by omega)
          (by rw [b1.2.2, hcc']) (by rw [hcc', b2.2.2])
    have hkey := V002.card_le_of_gaps_ne SF c W hWN hgapW
    omega
  -- the colour classes partition `[1, m]`
  have hsum : ∑ c : Fin (i + 2),
      ((Finset.Icc 1 m).filter (fun x => col x = c)).card = m := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := col) (s := Finset.Icc 1 m) (t := (Finset.univ : Finset (Fin (i + 2))))
      (fun x _ => Finset.mem_univ _)
    rw [Nat.card_Icc] at h
    omega
  have hle : ∀ c : Fin (i + 2),
      ((Finset.Icc 1 m).filter (fun x => col x = c)).card ≤ s := by
    intro c
    have := hW c
    omega
  have hsumle : ∑ c : Fin (i + 2), ((Finset.Icc 1 m).filter (fun x => col x = c)).card
      ≤ ∑ _c : Fin (i + 2), s := Finset.sum_le_sum (fun c _ => hle c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum] at hsumle
  omega

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := by
  intro k
  show SqueezeBench.Schur.f k
      ≤ (if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - k - 1 else V001.ram k - 2)
  by_cases hk : 3 ≤ k ∧ k % 2 = 1
  · rw [if_pos hk]
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
    have hr2 := V001.ram_ge_two (i + 1)
    -- `ram (i+1) - 1` is odd, because `i + 1` is even
    obtain ⟨t, ht⟩ : ∃ t, i + 1 = 2 * t := ⟨(i + 1) / 2, by omega⟩
    have hrs : V001.ram (i + 1) = (i + 1) * (V001.ram i - 1) + 2 := V001.ram_succ i
    have hprod : (i + 1) * (V001.ram i - 1) = 2 * (t * (V001.ram i - 1)) := by rw [ht]; ring
    obtain ⟨s, hsram⟩ : ∃ s, V001.ram (i + 1) = 2 * s + 2 :=
      ⟨(V001.ram (i + 1) - 2) / 2, by omega⟩
    have hle := f_le_of_forces (k := i + 2) (by simp [nMin]) (forces_half (i := i) (s := s) hsram)
    have hsub : V001.ram (i + 1) - 1 = 2 * s + 1 := by omega
    have hrs2 : V001.ram (i + 2) = (i + 2) * (V001.ram (i + 1) - 1) + 2 := V001.ram_succ (i + 1)
    have hexp : V001.ram (i + 2) = 2 * ((i + 2) * s) + (i + 2) + 2 := by
      rw [hrs2, hsub]; ring
    obtain ⟨p, hp⟩ : ∃ p, (i + 2) * s = p := ⟨_, rfl⟩
    rw [hp] at hexp hle
    omega
  · rw [if_neg hk]
    exact V001.valid k

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V002.record record := by
  intro k
  show (if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - k - 1 else V001.ram k - 2)
      ≤ (if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - 3 else V001.ram k - 2)
  split_ifs with hk
  · omega
  · exact le_rfl

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V002.record record :=
  ⟨3, by decide, by decide⟩

end SqueezeBench.Schur.Upper.V003
