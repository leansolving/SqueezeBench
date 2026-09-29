import SqueezeBench.Problems.Ramsey.Records.Lower.V007.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V006.Proof

/-! Record V007 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V007.lean`. The bound is the alteration form of Erdős' argument.
Summing V006's fibre bound over all colourings, some colouring `c` of the pairs of `Fin N`
is monochromatic on at most `d = ⌊2·C(N,n) / 2^C(n,2)⌋` of the `n`-sets; deleting one
vertex from each of them leaves at least `N − d` vertices, and the graph of `c` pulled back
along an injection `Fin M → Fin N` into the survivors has no monochromatic `n`-set for
any `M ≤ N − d`. So `f n ≥ N − d + 1` for every `N`; the record evaluates this at one
well-chosen `N`, with `d` bounded through `n!·C(N,n) ≤ N^n`. The colourings, the
monochromatic sets, their fibre count and the graph of a colouring are V006's. -/

namespace SqueezeBench.Ramsey.Lower.V007

open SqueezeBench SimpleGraph Finset

/-! ## Double counting -/

-- Summed over all colourings, the number of monochromatic `n`-sets is at most
-- `C(N,n) · 2 · 2^(N·N − C(n,2))`: swap the sums and use V006's fibre bound.
theorem sum_mono_le (N n : ℕ) :
    ∑ c : V006.Col N,
        ((powersetCard n (univ : Finset (Fin N))).filter (fun S => V006.Mono c S)).card
      ≤ N.choose n * (2 ^ (N * N - n.choose 2) * 2) := by
  have hcomm : ∑ c : V006.Col N,
        ((powersetCard n (univ : Finset (Fin N))).filter (fun S => V006.Mono c S)).card
      = ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
          (univ.filter (fun c : V006.Col N => V006.Mono c S)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hcomm]
  calc ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
          (univ.filter (fun c : V006.Col N => V006.Mono c S)).card
      ≤ ∑ S ∈ powersetCard n (univ : Finset (Fin N)), 2 ^ (N * N - n.choose 2) * 2 := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        rw [← (Finset.mem_powersetCard.mp hS).2]
        exact V006.card_mono_le S
    _ = N.choose n * (2 ^ (N * N - n.choose 2) * 2) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

-- The union bound with slack `d`: `C(N,n) · 2 · 2^(N·N − C(n,2)) < 2^(N·N) · (d + 1)`.
theorem count_lt {N n d : ℕ} (h : 2 * N.choose n < (d + 1) * 2 ^ n.choose 2) :
    N.choose n * (2 ^ (N * N - n.choose 2) * 2) < 2 ^ (N * N) * (d + 1) := by
  rcases Nat.lt_or_ge (N * N) (n.choose 2) with hlt | hle
  · have hNn : N < n := by
      by_contra hge
      have h1 : n.choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 (Nat.not_lt.mp hge)
      have h2 : N.choose 2 ≤ N * N := by
        rw [Nat.choose_two_right]
        exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      omega
    rw [Nat.choose_eq_zero_of_lt hNn, Nat.zero_mul]
    positivity
  · have hsplit : 2 ^ (N * N) = 2 ^ n.choose 2 * 2 ^ (N * N - n.choose 2) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hsplit, show N.choose n * (2 ^ (N * N - n.choose 2) * 2) =
      (2 * N.choose n) * 2 ^ (N * N - n.choose 2) from by ring,
      show 2 ^ n.choose 2 * 2 ^ (N * N - n.choose 2) * (d + 1) =
      ((d + 1) * 2 ^ n.choose 2) * 2 ^ (N * N - n.choose 2) from by ring]
    exact Nat.mul_lt_mul_of_pos_right h (by positivity)

-- Some colouring is monochromatic on at most `d` of the `n`-sets.
theorem exists_few {N n d : ℕ} (h : 2 * N.choose n < (d + 1) * 2 ^ n.choose 2) :
    ∃ c : V006.Col N,
      ((powersetCard n (univ : Finset (Fin N))).filter (fun S => V006.Mono c S)).card ≤ d := by
  have hlt : ∑ c : V006.Col N,
        ((powersetCard n (univ : Finset (Fin N))).filter (fun S => V006.Mono c S)).card
      < ∑ _c : V006.Col N, (d + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    exact lt_of_le_of_lt (sum_mono_le N n) (count_lt h)
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_of_sum_lt hlt
  exact ⟨c, Nat.lt_succ_iff.mp hc⟩

/-! ## The deletion -/

-- Delete one vertex from each monochromatic `n`-set of `c`; the graph of `c` pulled back
-- along an injection of `Fin M` into the survivors has no monochromatic `n`-set.
theorem not_forces_alt {N n d M : ℕ} (hn : 1 ≤ n) (c : V006.Col N)
    (hc : ((powersetCard n (univ : Finset (Fin N))).filter (fun S => V006.Mono c S)).card ≤ d)
    (hM : M ≤ N - d) : ¬ Forces M n n := by
  intro hF
  set B := (powersetCard n (univ : Finset (Fin N))).filter (fun S => V006.Mono c S) with hB
  have hne : ∀ S ∈ B, S.Nonempty := fun S hS => by
    have := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
    exact Finset.card_pos.mp (by omega)
  obtain ⟨D, hD, hDmem⟩ : ∃ D : Finset (Fin N), D.card ≤ d ∧
      ∀ S (hS : S ∈ B), S.min' (hne S hS) ∈ D :=
    ⟨B.attach.image (fun S => S.1.min' (hne S.1 S.2)),
      le_trans Finset.card_image_le (by rw [Finset.card_attach]; exact hc),
      fun S hS => Finset.mem_image.mpr ⟨⟨S, hS⟩, Finset.mem_attach _ _, rfl⟩⟩
  have hR : M ≤ Dᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨φ⟩ : Nonempty (Fin M ↪ ↥Dᶜ) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, Fintype.card_coe]; exact hR)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin M ↪ Fin N, ∀ i, ψ i ∉ D :=
    ⟨φ.trans (Function.Embedding.subtype _), fun i => Finset.mem_compl.mp (φ i).2⟩
  -- an `n`-set inside the image of `ψ` cannot be monochromatic: it would have lost a vertex
  have key : ∀ S : Finset (Fin M), S.card = n → V006.Mono c (S.map ψ) → False := by
    intro S hS hmono
    have hSB : S.map ψ ∈ B := Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by rw [Finset.card_map, hS]⟩, hmono⟩
    have hmin := Finset.min'_mem (S.map ψ) (hne _ hSB)
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hmin
    exact hψ i (by rw [hi]; exact hDmem _ hSB)
  rcases hF ((V006.graphOf c).comap ψ) with ⟨S, hS⟩ | ⟨T, hT⟩
  · refine key S hS.card_eq (Or.inl ?_)
    intro p hp
    rw [V006.mem_pairs] at hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_map.mp hp.1
    obtain ⟨b, hb, hpb⟩ := Finset.mem_map.mp hp.2.1
    have hab : a ≠ b := by
      rintro rfl
      have h12 : p.1 = p.2 := hpa.symm.trans hpb
      rw [h12] at hp
      exact lt_irrefl _ hp.2.2
    have hadj := hS.isClique ha hb hab
    rw [comap_adj, V006.graphOf_adj] at hadj
    rw [hpa, hpb, min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    exact hadj.2
  · refine key T hT.card_eq (Or.inr ?_)
    intro p hp
    rw [V006.mem_pairs] at hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_map.mp hp.1
    obtain ⟨b, hb, hpb⟩ := Finset.mem_map.mp hp.2.1
    have hab : a ≠ b := by
      rintro rfl
      have h12 : p.1 = p.2 := hpa.symm.trans hpb
      rw [h12] at hp
      exact lt_irrefl _ hp.2.2
    have hadj := hT.isClique ha hb hab
    rw [compl_adj, comap_adj, V006.graphOf_adj] at hadj
    rw [hpa, hpb, min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    by_contra hcp
    exact hadj.2 ⟨ne_of_lt hp.2.2, by simpa using hcp⟩

/-! ## The bound -/

-- For every `N`: `f n ≥ N − ⌊2·N^n / K⌋ + 1` with `K = n! · 2^C(n,2)`, because
-- `2·C(N,n) ≤ 2·N^n / n! < (⌊2·N^n / K⌋ + 1) · 2^C(n,2)`.
theorem main {n N K : ℕ} (hn2 : 2 ≤ n) (hK : K = n.factorial * 2 ^ n.choose 2) :
    N - 2 * N ^ n / K + 1 ≤ f n := by
  subst hK
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro M hM
  by_contra hcon
  have hMd : M ≤ N - 2 * N ^ n / (n.factorial * 2 ^ n.choose 2) := by omega
  have hKpos : 0 < n.factorial * 2 ^ n.choose 2 := by positivity
  have h1 : n.factorial * N.choose n ≤ N ^ n := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow N n
  have h2 : 2 * N ^ n < (2 * N ^ n / (n.factorial * 2 ^ n.choose 2) + 1) *
      (n.factorial * 2 ^ n.choose 2) := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add hKpos
  have h3 : n.factorial * (2 * N.choose n) <
      n.factorial * ((2 * N ^ n / (n.factorial * 2 ^ n.choose 2) + 1) * 2 ^ n.choose 2) := by
    calc n.factorial * (2 * N.choose n) = 2 * (n.factorial * N.choose n) := by ring
      _ ≤ 2 * N ^ n := Nat.mul_le_mul_left _ h1
      _ < (2 * N ^ n / (n.factorial * 2 ^ n.choose 2) + 1) * (n.factorial * 2 ^ n.choose 2) := h2
      _ = n.factorial * ((2 * N ^ n / (n.factorial * 2 ^ n.choose 2) + 1) * 2 ^ n.choose 2) := by
          ring
  obtain ⟨c, hc⟩ := exists_few (Nat.lt_of_mul_lt_mul_left h3)
  exact not_forces_alt (by omega) c hc hMd hM

theorem thr_eq (n : ℕ) : V006.thr n = n.factorial * 2 ^ n.choose 2 := by
  rw [V006.thr, V006.fact_eq, Nat.choose_two_right]

theorem alt_le {n : ℕ} (hn2 : 2 ≤ n) : alt n + 1 ≤ f n := by
  unfold alt altAt
  exact main hn2 (thr_eq n)

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  exact alt_le hn2

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V006.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 20) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V007
