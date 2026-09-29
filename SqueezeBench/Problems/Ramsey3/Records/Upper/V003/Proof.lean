import SqueezeBench.Problems.Ramsey3.Records.Upper.V003.Def
import SqueezeBench.Problems.Ramsey3.Records.Upper.V002.Proof

namespace SqueezeBench.Ramsey3.Upper.V003

open Finset SimpleGraph SqueezeBench SqueezeBench.Ramsey SqueezeBench.Ramsey3.Upper.V002

/-- Going up from `r`: `sh (r + j) ≥ sh r - j · del (r+1)`. -/
theorem secant_above (r : ℕ) : ∀ j : ℕ, sh r - (j : ℚ) * del (r + 1) ≤ sh (r + j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : del (r + j + 1) ≤ del (r + 1) := del_anti (by omega) (by omega)
    have h3 : del (r + j + 1) = sh (r + j) - sh (r + j + 1) := del_succ (r + j)
    have h4 : sh (r + (j + 1)) = sh (r + j + 1) := rfl
    rw [h4]
    push_cast
    linarith

/-- The secant line of `sh` through `r` and `r + 1` lies below `sh` everywhere. -/
theorem secant (r t : ℕ) : sh r + ((r : ℚ) - t) * del (r + 1) ≤ sh t := by
  rcases lt_trichotomy t r with h | rfl | h
  · have h1 := sh_sub_ge r (r - t) (Nat.sub_le r t)
    rw [Nat.sub_sub_self h.le] at h1
    have h2 : del (r + 1) ≤ del r := del_anti (by omega) (by omega)
    have h3 : ((r - t : ℕ) : ℚ) = (r : ℚ) - t := by rw [Nat.cast_sub h.le]
    rw [h3] at h1
    have h4 : (0 : ℚ) ≤ (r : ℚ) - t := by
      have : (t : ℚ) ≤ r := by exact_mod_cast h.le
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  · simp
  · obtain ⟨j, rfl⟩ : ∃ j, t = r + j := ⟨t - r, by omega⟩
    have := secant_above r j
    have e : ((r : ℚ) - ((r + j : ℕ) : ℚ)) * del (r + 1) = -((j : ℚ) * del (r + 1)) := by
      push_cast; ring
    rw [e]
    linarith

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adding `v` to an independent subset of its non-neighbourhood. -/
theorem insert_indep {S T' : Finset V} {v : V} (hv : v ∈ S) (hT' : T' ⊆ non G S v)
    (hind : G.IsIndepSet (T' : Set V)) :
    insert v T' ⊆ S ∧ G.IsIndepSet ((insert v T' : Finset V) : Set V) ∧
      (insert v T').card = T'.card + 1 := by
  have hvT' : v ∉ T' := fun h => not_mem_non G v (hT' h)
  refine ⟨Finset.insert_subset hv (hT'.trans (Finset.filter_subset _ _)), ?_,
    Finset.card_insert_of_notMem hvT'⟩
  rw [Finset.coe_insert, isIndepSet_iff, Set.pairwise_insert]
  refine ⟨hind, fun b hb _ => ?_⟩
  have hb' := (mem_non G).mp (hT' hb)
  exact ⟨hb'.2.1, fun h => hb'.2.1 ((G.adj_comm b v).mp h)⟩

/-- `|S ∖ N[v]| = |S| - 1 - deg v`. -/
theorem card_non {S : Finset V} {v : V} (hv : v ∈ S) :
    ((non G S v).card : ℚ) = (S.card : ℚ) - 1 - (nbr G S v).card := by
  have := sum_split G hv (fun _ => (1 : ℚ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  linarith

/-- The total degree of the graphs `G[S ∖ N[v]]`, summed over `v`: `Σ_u deg u (|S| - 2 deg u)`. -/
theorem sum_deg_non (htf : G.CliqueFree 3) (S : Finset V) :
    ∑ v ∈ S, ∑ u ∈ non G S v, ((nbr G (non G S v) u).card : ℚ)
      = ∑ u ∈ S, ((nbr G S u).card : ℚ) * ((S.card : ℚ) - 2 * (nbr G S u).card) := by
  have hA : ∀ v ∈ S, ∑ u ∈ non G S v, ((nbr G (non G S v) u).card : ℚ)
      = ∑ u ∈ non G S v, (((nbr G S u).card : ℚ) - (com G S u v).card) := by
    intro v _
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have h : ((nbr G (non G S v) u).card : ℚ) + (com G S u v).card = (nbr G S u).card := by
      exact_mod_cast card_nbr_non G hu
    linarith
  rw [Finset.sum_congr rfl hA,
    sum_non G S (fun u v => ((nbr G S u).card : ℚ) - (com G S u v).card)]
  have hB : ∀ u ∈ S, ∑ v ∈ non G S u, (((nbr G S u).card : ℚ) - (com G S u v).card)
      = ((nbr G S u).card : ℚ) * ((S.card : ℚ) - (nbr G S u).card)
        - ∑ w ∈ nbr G S u, ((nbr G S w).card : ℚ) := by
    intro u hu
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_non G hu]
    have hc : (∑ v ∈ non G S u, ((com G S u v).card : ℚ)) + ((nbr G S u).card : ℚ)
        = ∑ w ∈ nbr G S u, ((nbr G S w).card : ℚ) := by exact_mod_cast count_walks G htf hu
    linear_combination (-1 : ℚ) * hc
  rw [Finset.sum_congr rfl hB, Finset.sum_sub_distrib,
    sum_nbr G S (fun w => ((nbr G S w).card : ℚ)), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- The averaged deletion bound: with all degrees at most `D` and `|S| ≥ 4D`, some independent
set has at least `1 + a (n - 1 - D) - β D (n - 2D)` elements, `β = del (r+1)`, `a = sh r + r β`. -/
theorem deletion_bound (htf : G.CliqueFree 3) {S : Finset V} (hS : S.Nonempty) {D r : ℕ}
    (hD : ∀ u ∈ S, (nbr G S u).card ≤ D) (hn : 4 * D ≤ S.card) :
    ∃ T ⊆ S, G.IsIndepSet (T : Set V) ∧
      1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - D)
        - del (r + 1) * D * ((S.card : ℚ) - 2 * D) ≤ (T.card : ℚ) := by
  have hβ : 0 ≤ del (r + 1) := del_nonneg _
  have ha : 0 ≤ sh r + r * del (r + 1) := by
    have := sh_pos r
    positivity
  have local_bound : ∀ v ∈ S, ∃ T ⊆ S, G.IsIndepSet (T : Set V) ∧
      1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ)) ≤ (T.card : ℚ) := by
    intro v hv
    obtain ⟨T', hT'W, hT'ind, hT'card⟩ := shearer_indep G htf (non G S v)
    obtain ⟨h1, h2, h3⟩ := insert_indep G hv hT'W hT'ind
    refine ⟨insert v T', h1, h2, ?_⟩
    rw [h3]
    push_cast
    have h4 : ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ))
        ≤ ∑ u ∈ non G S v, sh (nbr G (non G S v) u).card := by
      refine Finset.sum_le_sum (fun u _ => ?_)
      have := secant r (nbr G (non G S v) u).card
      linarith
    linarith
  have hA : ∀ v ∈ S, ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ))
      = (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S v).card)
        - del (r + 1) * ∑ u ∈ non G S v, ((nbr G (non G S v) u).card : ℚ) := by
    intro v hv
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, card_non G hv]
    ring
  have hL : ∑ v ∈ S, (1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ)))
      = ∑ v ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S v).card))
        - del (r + 1) * ∑ v ∈ S, ∑ u ∈ non G S v, ((nbr G (non G S v) u).card : ℚ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hA v hv]
    ring
  have hR : ∑ v ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - D)
        - del (r + 1) * D * ((S.card : ℚ) - 2 * D))
      ≤ ∑ v ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - (nbr G S v).card))
        - del (r + 1) * ∑ u ∈ S, ((nbr G S u).card : ℚ) * ((S.card : ℚ) - 2 * (nbr G S u).card) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun u hu => ?_)
    have hd : ((nbr G S u).card : ℚ) ≤ D := by exact_mod_cast hD u hu
    have hn' : 4 * (D : ℚ) ≤ S.card := by exact_mod_cast hn
    have hd0 : (0 : ℚ) ≤ (nbr G S u).card := by positivity
    have key : 0 ≤ ((D : ℚ) - (nbr G S u).card) * ((sh r + r * del (r + 1))
        + del (r + 1) * ((S.card : ℚ) - 2 * (((nbr G S u).card : ℚ) + D))) := by
      apply mul_nonneg (by linarith)
      apply add_nonneg ha
      apply mul_nonneg hβ
      linarith
    nlinarith [key]
  have hsum : ∑ v ∈ S, (1 + (sh r + r * del (r + 1)) * ((S.card : ℚ) - 1 - D)
        - del (r + 1) * D * ((S.card : ℚ) - 2 * D))
      ≤ ∑ v ∈ S, (1 + ∑ u ∈ non G S v, ((sh r + r * del (r + 1))
        - del (r + 1) * ((nbr G (non G S v) u).card : ℚ))) := by
    rw [hL, sum_deg_non G htf S]
    exact hR
  obtain ⟨v, hv, hvle⟩ := Finset.exists_le_of_sum_le hS hsum
  obtain ⟨T, hT, hind, hLv⟩ := local_bound v hv
  exact ⟨T, hT, hind, le_trans hvle hLv⟩

/-- `del (r+1)` and `sh r` over the common denominator `q(r+1)`. -/
theorem shearer_succ_le (r : ℕ) :
    (shearer (r + 1)).1 ≤ (shearer r).1 * ((r + 1) * (r + 1) + 1) := by
  have h := del_nonneg (r + 1)
  rw [del_succ] at h
  unfold sh at h
  have hq : (0 : ℚ) < (shearer r).2 := by exact_mod_cast (shearer_pos r).2
  have hq' : (0 : ℚ) < (shearer (r + 1)).2 := by exact_mod_cast (shearer_pos (r + 1)).2
  rw [sub_nonneg, div_le_div_iff₀ hq' hq] at h
  have e : ((shearer (r + 1)).2 : ℚ) = ((r + 1) * (r + 1) + 1) * (shearer r).2 := by
    simp [shearer]
  rw [e] at h
  have h2 : ((shearer (r + 1)).1 : ℚ) ≤ (shearer r).1 * ((r + 1) * (r + 1) + 1) := by
    nlinarith [hq]
  exact_mod_cast h2

theorem del_succ_eq (r : ℕ) :
    del (r + 1) = (((shearer r).1 * ((r + 1) * (r + 1) + 1) - (shearer (r + 1)).1 : ℕ) : ℚ)
      / (shearer (r + 1)).2 := by
  rw [del_succ, Nat.cast_sub (shearer_succ_le r)]
  unfold sh
  have hq : (0 : ℚ) < (shearer r).2 := by exact_mod_cast (shearer_pos r).2
  have e : ((shearer (r + 1)).2 : ℚ) = ((r + 1) * (r + 1) + 1) * (shearer r).2 := by
    simp [shearer]
  rw [e]
  push_cast
  field_simp

theorem sh_eq_over (r : ℕ) :
    sh r = ((shearer r).1 * ((r + 1) * (r + 1) + 1) : ℚ) / (shearer (r + 1)).2 := by
  unfold sh
  have hq : (0 : ℚ) < (shearer r).2 := by exact_mod_cast (shearer_pos r).2
  have e : ((shearer (r + 1)).2 : ℚ) = ((r + 1) * (r + 1) + 1) * (shearer r).2 := by
    simp [shearer]
  rw [e]
  field_simp

/-- The arithmetic behind `cand`: with `a = A/q'`, `β = B/q'`, the averaged deletion bound
`1 + a (n - 1 - D) - β D (n - 2D) ≤ D` contradicts `n ≥ ⌊X⌋ + 1`. -/
theorem cand_arith (D n A B q' : ℕ) (hD : 1 ≤ D) (hq' : 0 < q') (hslope : ¬ A ≤ B * D)
    (hcard : ((D - 1) * q' + A * (D + 1) - 2 * B * D * D) / (A - B * D) + 1 ≤ n)
    (hineq : 1 + ((A : ℚ) / q') * ((n : ℚ) - 1 - D) - (B : ℚ) / q' * D * ((n : ℚ) - 2 * D)
      ≤ D) : False := by
  have hq'q : (0 : ℚ) < q' := by exact_mod_cast hq'
  have hslope' : B * D < A := Nat.lt_of_not_le hslope
  have hD1 : ((D - 1 : ℕ) : ℚ) = (D : ℚ) - 1 := by rw [Nat.cast_sub hD]; push_cast; ring
  have key : (n : ℚ) * ((A : ℚ) - B * D)
      ≤ ((D : ℚ) - 1) * q' + A * (D + 1) - 2 * B * D * D := by
    have h2 := mul_le_mul_of_nonneg_left hineq hq'q.le
    have h3 : (q' : ℚ) * (1 + ((A : ℚ) / q') * ((n : ℚ) - 1 - D)
        - (B : ℚ) / q' * D * ((n : ℚ) - 2 * D))
        = q' + (A : ℚ) * ((n : ℚ) - 1 - D) - (B : ℚ) * D * ((n : ℚ) - 2 * D) := by
      field_simp
      try ring
    rw [h3] at h2
    nlinarith [h2]
  have hnum : ((D : ℚ) - 1) * q' + A * (D + 1) - 2 * B * D * D
      ≤ (((D - 1) * q' + A * (D + 1) - 2 * B * D * D : ℕ) : ℚ) := by
    rcases Nat.lt_or_ge ((D - 1) * q' + A * (D + 1)) (2 * B * D * D) with h | h
    swap
    · rw [Nat.cast_sub h]
      push_cast
      rw [hD1]
    · rw [Nat.sub_eq_zero_of_le h.le]
      have h' : (((D - 1) * q' + A * (D + 1) : ℕ) : ℚ) < ((2 * B * D * D : ℕ) : ℚ) := by
        exact_mod_cast h
      push_cast at h'
      rw [hD1] at h'
      push_cast
      linarith
  have hden : ((A - B * D : ℕ) : ℚ) = (A : ℚ) - B * D := by
    rw [Nat.cast_sub hslope'.le]; push_cast; ring
  have hlt := Nat.lt_mul_div_succ ((D - 1) * q' + A * (D + 1) - 2 * B * D * D)
    (show 0 < A - B * D by omega)
  have hlt2 : ((D - 1) * q' + A * (D + 1) - 2 * B * D * D) < (A - B * D) * n :=
    lt_of_lt_of_le hlt (Nat.mul_le_mul_left _ hcard)
  have hlt3 : ((((D - 1) * q' + A * (D + 1) - 2 * B * D * D : ℕ)) : ℚ)
      < ((A - B * D : ℕ) : ℚ) * n := by exact_mod_cast hlt2
  rw [hden] at hlt3
  nlinarith [key, hnum, hlt3]

/-- Each candidate forces. -/
theorem forcesOn_cand (D r fb : ℕ) (hD : 1 ≤ D) (hfb : ForcesOn fb 3 (D + 1)) :
    ForcesOn (cand D r fb) 3 (D + 1) := by
  intro V _ _ G hcard
  unfold cand at hcard
  dsimp only at hcard
  split_ifs at hcard with hslope
  · exact hfb G hcard
  · classical
    by_contra hcon
    obtain ⟨hS, hT⟩ := not_or.mp hcon
    have htf : G.CliqueFree 3 := not_exists.mp hS
    have hT' : ∀ T : Finset V, ¬ Gᶜ.IsNClique (D + 1) T := not_exists.mp hT
    have hind : ∀ T : Finset V, G.IsIndepSet (T : Set V) → T.card ≤ D := by
      intro T hTind
      by_contra h
      obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq (show D + 1 ≤ T.card by omega)
      refine hT' T' ⟨?_, hT'card⟩
      rw [isClique_compl]
      exact hTind.mono (Finset.coe_subset.mpr hT'T)
    have hdeg : ∀ u ∈ (univ : Finset V), (nbr G univ u).card ≤ D := by
      intro u _
      apply hind
      intro a ha b hb _ hadj
      rw [Finset.mem_coe, mem_nbr] at ha hb
      exact no_triangle G htf ha.2 hadj hb.2
    have hn4 : 4 * D ≤ Fintype.card V := le_trans (le_max_left _ _) hcard
    have hne : (univ : Finset V).Nonempty :=
      Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
    obtain ⟨T, _, hTind, hTbound⟩ :=
      deletion_bound G htf hne (D := D) (r := r) hdeg (by rw [Finset.card_univ]; exact hn4)
    have hTD : (T.card : ℚ) ≤ D := by exact_mod_cast hind T hTind
    rw [Finset.card_univ] at hTbound
    have hdel : del (r + 1) = (((shearer r).1 * ((r + 1) * (r + 1) + 1) - (shearer (r + 1)).1 : ℕ)
        : ℚ) / (shearer (r + 1)).2 := del_succ_eq r
    have hsh : sh r = (((shearer r).1 * ((r + 1) * (r + 1) + 1) : ℕ) : ℚ)
        / (shearer (r + 1)).2 := by
      rw [sh_eq_over r]
      push_cast
      try ring
    have ha : sh r + r * del (r + 1) = (((shearer r).1 * ((r + 1) * (r + 1) + 1)
        + r * ((shearer r).1 * ((r + 1) * (r + 1) + 1) - (shearer (r + 1)).1) : ℕ) : ℚ)
        / (shearer (r + 1)).2 := by
      rw [hdel, hsh]
      push_cast
      ring
    rw [ha, hdel] at hTbound
    exact cand_arith D (Fintype.card V) _ _ _ hD (shearer_pos (r + 1)).2 hslope
      (le_trans (le_max_right _ _) hcard) (le_trans hTbound hTD)

theorem forcesOn_min {a b s t : ℕ} (ha : ForcesOn a s t) (hb : ForcesOn b s t) :
    ForcesOn (min a b) s t := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

theorem forcesOn_foldl (D fb : ℕ) (hD : 1 ≤ D) (hfb : ForcesOn fb 3 (D + 1)) :
    ∀ (l : List ℕ) (init : ℕ), ForcesOn init 3 (D + 1) →
      ForcesOn (l.foldl (fun acc r => min acc (cand D r fb)) init) 3 (D + 1) := by
  intro l
  induction l with
  | nil => intro init h; exact h
  | cons r l ih =>
    intro init h
    simp only [List.foldl_cons]
    exact ih _ (forcesOn_min h (forcesOn_cand D r fb hD hfb))

theorem forcesOn_v (k : ℕ) (hk : 2 ≤ k) : ForcesOn (v k) 3 k := by
  obtain ⟨D, rfl⟩ : ∃ D, k = D + 1 := ⟨k - 1, by omega⟩
  have hD : 1 ≤ D := by omega
  have hfb : ForcesOn (SqueezeBench.Ramsey3.Upper.V002.v (D + 1)) 3 (D + 1) :=
    SqueezeBench.Ramsey3.Upper.V002.forcesOn_v (D + 1) (by omega)
  -- every `ForcesOn` fact is ascribed: the relation opens with implicit binders
  have t1 : ∀ (l : List ℕ) (init : ℕ), ForcesOn init 3 (D + 1) →
      ForcesOn (l.foldl (fun acc r => min acc (cand D r (SqueezeBench.Ramsey3.Upper.V002.v (D + 1))))
        init) 3 (D + 1) :=
    forcesOn_foldl D (SqueezeBench.Ramsey3.Upper.V002.v (D + 1)) hD hfb
  have t2 : ForcesOn ((List.range (D + 1)).foldl
      (fun acc r => min acc (cand D r (SqueezeBench.Ramsey3.Upper.V002.v (D + 1))))
      (SqueezeBench.Ramsey3.Upper.V002.v (D + 1))) 3 (D + 1) :=
    t1 (List.range (D + 1)) (SqueezeBench.Ramsey3.Upper.V002.v (D + 1)) hfb
  show ForcesOn ((List.range (D + 1)).foldl
      (fun acc r => min acc (cand (D + 1 - 1) r (SqueezeBench.Ramsey3.Upper.V002.v (D + 1))))
      (SqueezeBench.Ramsey3.Upper.V002.v (D + 1))) 3 (D + 1)
  simp only [Nat.add_sub_cancel]
  exact t2

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f v := by
  intro k
  rcases Nat.lt_or_ge k SqueezeBench.Ramsey3.nMin with h | h
  · rw [SqueezeBench.Ramsey3.f, if_pos h]
    exact Nat.zero_le _
  · exact SqueezeBench.Ramsey3.f_le_of_forces h (Ramsey.forces_of_forcesOn (forcesOn_v k h))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Ramsey3.Upper.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey3.Upper.V002.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Upper.V002.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 8) (by decide) (by decide)

end SqueezeBench.Ramsey3.Upper.V003
