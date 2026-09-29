import SqueezeBench.Problems.Schur.Records.Upper.V002.Def
import SqueezeBench.Problems.Schur.Records.Upper.V001.Proof

/-! Record V002 for Schur, upper direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Schur/Upper/V002.lean`. -/

namespace SqueezeBench.Schur.Upper.V002

open SqueezeBench Finset SqueezeBench.Schur

-- A set of points in `[0, N]` whose pairwise gaps all avoid one colour carries a
-- `(k-1)`-colouring of its pairs, so it has at most `ram (k-1) - 1` points.
theorem card_le_of_gaps_ne {i N : ℕ} {col : ℕ → Fin (i + 2)}
    (SF : ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → z ≤ N → x + y = z →
      col x = col y → col y = col z → False)
    (c₀ : Fin (i + 2)) (X : Finset ℕ) (hXN : ∀ u ∈ X, u ≤ N)
    (hgap : ∀ u ∈ X, ∀ w ∈ X, u < w → col (w - u) ≠ c₀) :
    X.card ≤ V001.ram (i + 1) - 1 := by
  classical
  by_contra hlt
  have hr2 := V001.ram_ge_two (i + 1)
  have hcard : V001.ram (i + 1) ≤ Fintype.card ↥X := by
    rw [Fintype.card_coe]; omega
  set col' : ↥X → ↥X → Fin (i + 1) :=
    fun u w => Function.invFun (Fin.succAbove c₀)
      (col (max (u : ℕ) (w : ℕ) - min (u : ℕ) (w : ℕ))) with hcol'
  have hsym' : ∀ u w : ↥X, col' u w = col' w u := by
    intro u w
    simp only [hcol', max_comm (u : ℕ) (w : ℕ), min_comm (u : ℕ) (w : ℕ)]
  obtain ⟨ι, S, hS3, hSmono⟩ := V001.monoTriangle_ram i col' hsym' hcard
  set T : Finset ℕ := S.image (fun p : ↥X => (p : ℕ)) with hT
  have hTcard : T.card = 3 := by
    rw [hT, Finset.card_image_of_injective _ Subtype.coe_injective, hS3]
  set u : Fin 3 → ℕ := fun t => (T.orderIsoOfFin hTcard t : ℕ) with hu
  have hult : ∀ s t : Fin 3, s < t → u s < u t := by
    intro s t hst
    have h : ((T.orderIsoOfFin hTcard s : ℕ)) < ((T.orderIsoOfFin hTcard t : ℕ)) := by
      exact_mod_cast (T.orderIsoOfFin hTcard).lt_iff_lt.mpr hst
    exact h
  have hback : ∀ t : Fin 3, ∃ p, p ∈ S ∧ (p : ℕ) = u t := by
    intro t
    have hm : u t ∈ T := (T.orderIsoOfFin hTcard t).2
    rw [hT, Finset.mem_image] at hm
    obtain ⟨p, hp, hpv⟩ := hm
    exact ⟨p, hp, hpv⟩
  have hb : ∀ t : Fin 3, u t ≤ N := by
    intro t
    obtain ⟨p, -, hpv⟩ := hback t
    rw [← hpv]; exact hXN _ p.2
  have hcolu : ∀ s t : Fin 3, s < t → col (u t - u s) = Fin.succAbove c₀ ι := by
    intro s t hst
    obtain ⟨p, hp, hpv⟩ := hback s
    obtain ⟨q, hq, hqv⟩ := hback t
    have hlt' := hult s t hst
    have hpqlt : (p : ℕ) < (q : ℕ) := by rw [hpv, hqv]; exact hlt'
    have hpq : p ≠ q := by
      intro he; rw [he] at hpqlt; omega
    have hmm : max (p : ℕ) (q : ℕ) - min (p : ℕ) (q : ℕ) = u t - u s := by
      rw [max_eq_right (le_of_lt hpqlt), min_eq_left (le_of_lt hpqlt), hpv, hqv]
    have hne : col (u t - u s) ≠ c₀ := by
      have h := hgap (p : ℕ) p.2 (q : ℕ) q.2 hpqlt
      rw [hpv, hqv] at h
      exact h
    have hex : ∃ z, Fin.succAbove c₀ z = col (u t - u s) := Fin.exists_succAbove_eq hne
    have heq := Function.invFun_eq hex
    have hdef : col' p q = Function.invFun (Fin.succAbove c₀)
        (col (max (p : ℕ) (q : ℕ) - min (p : ℕ) (q : ℕ))) := rfl
    rw [hmm] at hdef
    rw [← hdef, hSmono p hp q hq hpq] at heq
    exact heq.symm
  have h01 := hult 0 1 (by decide)
  have h12 := hult 1 2 (by decide)
  have h02 := hult 0 2 (by decide)
  have hb2 := hb 2
  exact SF (u 1 - u 0) (u 2 - u 1) (u 2 - u 0) (by omega) (by omega) (by omega) (by omega)
    (by rw [hcolu 0 1 (by decide), hcolu 1 2 (by decide)])
    (by rw [hcolu 1 2 (by decide), hcolu 0 2 (by decide)])

-- For odd `k = i + 2 ≥ 3` the extremal case of the Ramsey chain is impossible: every colour
-- class would have to contain the midpoint of `[1, N]`.
theorem forces_parity {i : ℕ} (hpar : (i + 1) % 2 = 0) :
    Forces (i + 2) ((i + 2) * (V001.ram (i + 1) - 1)) := by
  classical
  have hr2 := V001.ram_ge_two (i + 1)
  set a := V001.ram (i + 1) - 1 with ha
  set N := (i + 2) * a with hNdef
  have ha1 : 1 ≤ a := by omega
  have hipos : 1 ≤ i := by omega
  -- `a` is odd because `a = (i+1) * (ram i - 1) + 1` and `i + 1` is even
  obtain ⟨t, ht⟩ : ∃ t, i + 1 = 2 * t := ⟨(i + 1) / 2, by omega⟩
  have hrs : V001.ram (i + 1) = (i + 1) * (V001.ram i - 1) + 2 := V001.ram_succ i
  have hprod : (i + 1) * (V001.ram i - 1) = 2 * (t * (V001.ram i - 1)) := by rw [ht]; ring
  have haodd : a % 2 = 1 := by omega
  obtain ⟨s, hs⟩ : ∃ s, a = 2 * s + 1 := ⟨a / 2, by omega⟩
  have hi2 : i + 2 = 2 * t + 1 := by omega
  set m := 2 * t * s + t + s + 1 with hm
  have hNm : N + 1 = 2 * m := by rw [hNdef, hi2, hs, hm]; ring
  have hm1 : 1 ≤ m := by omega
  intro col
  by_contra hno
  have SF : ∀ x y z : ℕ, 1 ≤ x → 1 ≤ y → z ≤ N → x + y = z →
      col x = col y → col y = col z → False := by
    intro x y z hx hy hz hxy h1 h2
    exact hno ⟨x, by rw [Finset.mem_Icc]; omega, y, by rw [Finset.mem_Icc]; omega,
      z, by rw [Finset.mem_Icc]; omega, hxy, h1, h2⟩
  -- the colour-`c` neighbourhood of the vertex `m - 1` in the gap colouring
  have hW : ∀ c : Fin (i + 2),
      ((Finset.Icc 1 (m - 1)).filter (fun x => col x = c)).card
        + ((Finset.Icc 1 m).filter (fun x => col x = c)).card ≤ a := by
    intro c
    set v := m - 1 with hv
    set Pv := (Finset.Icc 1 v).filter (fun x => col x = c) with hPv
    set Pw := (Finset.Icc 1 m).filter (fun x => col x = c) with hPw
    have hPvb : ∀ x ∈ Pv, 1 ≤ x ∧ x ≤ v ∧ col x = c := by
      intro x hx
      rw [hPv, Finset.mem_filter, Finset.mem_Icc] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    have hPwb : ∀ x ∈ Pw, 1 ≤ x ∧ x ≤ m ∧ col x = c := by
      intro x hx
      rw [hPw, Finset.mem_filter, Finset.mem_Icc] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    set W := Pv.image (fun x => v - x) ∪ Pw.image (fun x => v + x) with hWdef
    have hdisj : Disjoint (Pv.image (fun x => v - x)) (Pw.image (fun x => v + x)) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hy1
      obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hy2
      have b1 := hPvb x1 hx1
      have b2 := hPwb x2 hx2
      omega
    have hi1 : (Pv.image (fun x => v - x)).card = Pv.card := by
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      have b1 := hPvb x (Finset.mem_coe.mp hx)
      have b2 := hPvb y (Finset.mem_coe.mp hy)
      have hxy' : v - x = v - y := hxy
      omega
    have hi2' : (Pw.image (fun x => v + x)).card = Pw.card := by
      refine Finset.card_image_of_injOn ?_
      intro x _ y _ hxy
      have hxy' : v + x = v + y := hxy
      omega
    have hcardW : W.card = Pv.card + Pw.card := by
      rw [hWdef, Finset.card_union_of_disjoint hdisj, hi1, hi2']
    have hWN : ∀ y ∈ W, y ≤ N := by
      intro y hy
      rw [hWdef, Finset.mem_union] at hy
      rcases hy with h | h
      · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
        have b := hPvb x hx
        omega
      · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
        have b := hPwb x hx
        omega
    have hgapW : ∀ p ∈ W, ∀ q ∈ W, p < q → col (q - p) ≠ c := by
      intro p hp q hq hpq hcc
      rw [hWdef, Finset.mem_union] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPvb x1 hx1
        have b2 := hPvb x2 hx2
        have hcc' : col (x1 - x2) = c := by
          rw [show x1 - x2 = q - p from by omega]; exact hcc
        exact SF x2 (x1 - x2) x1 (by omega) (by omega) (by omega) (by omega)
          (by rw [b2.2.2, hcc']) (by rw [hcc', b1.2.2])
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPvb x1 hx1
        have b2 := hPwb x2 hx2
        have hcc' : col (x1 + x2) = c := by
          rw [show x1 + x2 = q - p from by omega]; exact hcc
        exact SF x1 x2 (x1 + x2) (by omega) (by omega) (by omega) (by omega)
          (by rw [b1.2.2, b2.2.2]) (by rw [b2.2.2, hcc'])
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPwb x1 hx1
        have b2 := hPvb x2 hx2
        omega
      · obtain ⟨x1, hx1, he1⟩ := Finset.mem_image.mp hp
        obtain ⟨x2, hx2, he2⟩ := Finset.mem_image.mp hq
        have b1 := hPwb x1 hx1
        have b2 := hPwb x2 hx2
        have hcc' : col (x2 - x1) = c := by
          rw [show x2 - x1 = q - p from by omega]; exact hcc
        exact SF x1 (x2 - x1) x2 (by omega) (by omega) (by omega) (by omega)
          (by rw [b1.2.2, hcc']) (by rw [hcc', b2.2.2])
    have hkey := card_le_of_gaps_ne SF c W hWN hgapW
    omega
  -- the colour classes of `[1, m-1]` and of `[1, m]` partition those intervals
  have hs1 : ∑ c : Fin (i + 2),
      ((Finset.Icc 1 (m - 1)).filter (fun x => col x = c)).card = m - 1 := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := col) (s := Finset.Icc 1 (m - 1)) (t := (Finset.univ : Finset (Fin (i + 2))))
      (fun x _ => Finset.mem_univ _)
    rw [Nat.card_Icc] at h
    omega
  have hs2 : ∑ c : Fin (i + 2),
      ((Finset.Icc 1 m).filter (fun x => col x = c)).card = m := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := col) (s := Finset.Icc 1 m) (t := (Finset.univ : Finset (Fin (i + 2))))
      (fun x _ => Finset.mem_univ _)
    rw [Nat.card_Icc] at h
    omega
  -- `N = (i+2) * a` with `i+2` classes each of size at most `a` pins every class
  have heach : ∀ c : Fin (i + 2),
      ((Finset.Icc 1 (m - 1)).filter (fun x => col x = c)).card
        + ((Finset.Icc 1 m).filter (fun x => col x = c)).card = a := by
    intro c
    by_contra hne
    have hsumlt : (∑ c' : Fin (i + 2),
        (((Finset.Icc 1 (m - 1)).filter (fun x => col x = c')).card
          + ((Finset.Icc 1 m).filter (fun x => col x = c')).card))
        < ∑ _c' : Fin (i + 2), a :=
      Finset.sum_lt_sum (fun c' _ => hW c') ⟨c, Finset.mem_univ c, lt_of_le_of_ne (hW c) hne⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsumlt
    rw [Finset.sum_add_distrib, hs1, hs2] at hsumlt
    omega
  -- passing from `[1, m-1]` to `[1, m]` adds the midpoint `m`, so `a` and that indicator
  -- have the same parity
  have hstep : ∀ c : Fin (i + 2),
      ((Finset.Icc 1 m).filter (fun x => col x = c)).card
        = ((Finset.Icc 1 (m - 1)).filter (fun x => col x = c)).card
          + (if col m = c then 1 else 0) := by
    intro c
    have hins : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.filter_insert]
    by_cases hc : col m = c
    · rw [if_pos hc, if_pos hc,
        Finset.card_insert_of_notMem (by
          intro hmem
          rw [Finset.mem_filter, Finset.mem_Icc] at hmem
          omega)]
    · rw [if_neg hc, if_neg hc]
      omega
  have hall : ∀ c : Fin (i + 2), (if col m = c then 1 else 0) = 1 := by
    intro c
    have h1 := heach c
    have h2 := hstep c
    by_cases hc : col m = c
    · rw [if_pos hc]
    · rw [if_neg hc] at h2
      omega
  have hone : ∑ c : Fin (i + 2), (if col m = c then 1 else 0) = 1 := by simp
  rw [Finset.sum_congr rfl (fun c _ => hall c), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hone
  omega

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Schur.f record := by
  intro k
  show SqueezeBench.Schur.f k ≤ (if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - 3 else V001.ram k - 2)
  by_cases hk : 3 ≤ k ∧ k % 2 = 1
  · rw [if_pos hk]
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
    have hpar : (i + 1) % 2 = 0 := by omega
    have hle := f_le_of_forces (k := i + 2) (by simp [nMin]) (forces_parity hpar)
    have hrs : V001.ram (i + 2) = (i + 2) * (V001.ram (i + 1) - 1) + 2 := V001.ram_succ (i + 1)
    omega
  · rw [if_neg hk]
    exact V001.valid k

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Schur.Upper.V001.record record := by
  intro k
  show (if 3 ≤ k ∧ k % 2 = 1 then V001.ram k - 3 else V001.ram k - 2) ≤ V001.ram k - 2
  split <;> omega

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Schur.nMin SqueezeBench.Schur.Upper.V001.record record :=
  ⟨3, by decide, by decide⟩

end SqueezeBench.Schur.Upper.V002
