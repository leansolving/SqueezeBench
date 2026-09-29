import SqueezeBench.Problems.Ramsey.Records.Lower.V006.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V005.Proof

/-! Record V006 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V006.lean`. The bound is Erdős' counting argument (1947). A
2-colouring of the pairs of `Fin N` is read off a function on ordered pairs, of which there
are `2^(N·N)`; for a fixed `n`-set at most `2 · 2^(N·N − C(n,2))` of them are monochromatic
on it, so when `2 · C(N,n) < 2^C(n,2)` some colouring has no monochromatic `n`-set, and the
graph it defines shows `¬ Forces N n n`. The record's search returns an `M` with
`2 · M^n < n! · 2^C(n,2)`, which implies the counting condition for every `N ≤ M`. -/

namespace SqueezeBench.Ramsey.Lower.V006

open SqueezeBench SimpleGraph Finset

/-! ## Colourings of ordered pairs -/

-- A colouring of the ordered pairs of `Fin N`; only the pairs `(x, y)` with `x < y` are read.
abbrev Col (N : ℕ) := Fin N × Fin N → Bool

-- The increasing pairs inside `S`.
def pairs {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (S ×ˢ S).filter (fun p => p.1 < p.2)

theorem mem_pairs {N : ℕ} {S : Finset (Fin N)} {p : Fin N × Fin N} :
    p ∈ pairs S ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 := by
  simp [pairs, Finset.mem_filter, Finset.mem_product, and_assoc]

-- `S` has `C(|S|, 2)` increasing pairs: they correspond to its 2-subsets.
theorem card_pairs {N : ℕ} (S : Finset (Fin N)) : (pairs S).card = S.card.choose 2 := by
  rw [← Finset.card_powersetCard]
  refine Finset.card_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_
  · intro p hp
    rw [mem_pairs] at hp
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair (ne_of_lt hp.2.2)⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp.1
    · exact hp.2.1
  · intro p hp q hq hpq
    rw [mem_pairs] at hp hq
    have h1 : p.1 ∈ ({q.1, q.2} : Finset (Fin N)) := by rw [← hpq]; simp
    have h2 : p.2 ∈ ({q.1, q.2} : Finset (Fin N)) := by rw [← hpq]; simp
    have h3 : q.1 ∈ ({p.1, p.2} : Finset (Fin N)) := by rw [hpq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
    have hp' := Fin.lt_def.mp hp.2.2
    have hq' := Fin.lt_def.mp hq.2.2
    rw [Prod.ext_iff]
    simp only [Fin.ext_iff] at h1 h2 h3 ⊢
    omega
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp ht.2
    have hx : x ∈ S := ht.1 (by simp)
    have hy : y ∈ S := ht.1 (by simp)
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨(x, y), mem_pairs.mpr ⟨hx, hy, h⟩, rfl⟩
    · exact ⟨(y, x), mem_pairs.mpr ⟨hy, hx, h⟩, Finset.pair_comm _ _⟩

/-! ## Monochromatic sets and their count -/

-- `c` is constant on the increasing pairs inside `S`.
def Mono {N : ℕ} (c : Col N) (S : Finset (Fin N)) : Prop :=
  (∀ p ∈ pairs S, c p = true) ∨ (∀ p ∈ pairs S, c p = false)

instance {N : ℕ} (c : Col N) (S : Finset (Fin N)) : Decidable (Mono c S) := by
  unfold Mono; infer_instance

-- At most `2 · 2^(N·N − C(|S|,2))` colourings are monochromatic on `S`: such a colouring is
-- determined by its colour on `S` together with its values off the pairs of `S`.
theorem card_mono_le {N : ℕ} (S : Finset (Fin N)) :
    (Finset.univ.filter (fun c : Col N => Mono c S)).card ≤
      2 ^ (N * N - S.card.choose 2) * 2 := by
  have hcard : Fintype.card ((↥((pairs S)ᶜ) → Bool) × Bool) =
      2 ^ (N * N - S.card.choose 2) * 2 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_compl, card_pairs, Fintype.card_prod, Fintype.card_fin]
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun c : Col N => ((fun q : ↥((pairs S)ᶜ) => c q.1), decide (∀ p ∈ pairs S, c p = true)))
    (fun _ _ => Finset.mem_univ _) ?_
  intro c hc c' hc' h
  have hm : Mono c S := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
  have hm' : Mono c' S := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
  unfold Mono at hm hm'
  simp only [Prod.mk.injEq, decide_eq_decide] at h
  obtain ⟨h1, h2⟩ := h
  have hout : ∀ q, q ∉ pairs S → c q = c' q :=
    fun q hq => congrFun h1 ⟨q, Finset.mem_compl.mpr hq⟩
  funext p
  by_cases hp : p ∈ pairs S
  · rcases hm with hct | hcf
    · rw [hct p hp, h2.mp hct p hp]
    · have hnt : ¬ ∀ p ∈ pairs S, c p = true := fun hct => by
        have := hct p hp
        rw [hcf p hp] at this
        exact Bool.noConfusion this
      rcases hm' with hct' | hcf'
      · exact absurd (h2.mpr hct') hnt
      · rw [hcf p hp, hcf' p hp]
  · exact hout p hp

/-! ## The counting argument -/

-- The union bound is strict: `C(N,n) · 2 · 2^(N·N − C(n,2)) < 2^(N·N)`.
theorem count_lt {N n : ℕ} (h : 2 * N.choose n < 2 ^ n.choose 2) :
    N.choose n * (2 ^ (N * N - n.choose 2) * 2) < 2 ^ (N * N) := by
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
      (2 * N.choose n) * 2 ^ (N * N - n.choose 2) from by ring]
    exact Nat.mul_lt_mul_of_pos_right h (by positivity)

-- Some colouring is monochromatic on no `n`-set.
theorem exists_good {N n : ℕ} (h : 2 * N.choose n < 2 ^ n.choose 2) :
    ∃ c : Col N, ∀ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), ¬ Mono c S := by
  set bad := (Finset.powersetCard n (Finset.univ : Finset (Fin N))).biUnion
    (fun S => Finset.univ.filter (fun c : Col N => Mono c S)) with hbad_def
  have hbad : bad.card < (Finset.univ : Finset (Col N)).card := by
    calc bad.card
        ≤ ∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)),
            (Finset.univ.filter (fun c : Col N => Mono c S)).card := Finset.card_biUnion_le
      _ ≤ ∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)),
            2 ^ (N * N - n.choose 2) * 2 := by
          refine Finset.sum_le_sum (fun S hS => ?_)
          rw [← (Finset.mem_powersetCard.mp hS).2]
          exact card_mono_le S
      _ = N.choose n * (2 ^ (N * N - n.choose 2) * 2) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ < 2 ^ (N * N) := count_lt h
      _ = (Finset.univ : Finset (Col N)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
            Fintype.card_fin]
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  refine ⟨c, fun S hS hmono => hc ?_⟩
  exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmono⟩⟩

/-! ## The graph of a colouring -/

def graphOf {N : ℕ} (c : Col N) : SimpleGraph (Fin N) where
  Adj x y := x ≠ y ∧ c (min x y, max x y) = true
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [min_comm, max_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem graphOf_adj {N : ℕ} {c : Col N} {x y : Fin N} :
    (graphOf c).Adj x y ↔ x ≠ y ∧ c (min x y, max x y) = true := Iff.rfl

-- A clique of the graph, or of its complement, is a monochromatic set of the colouring.
theorem not_forces {N n : ℕ} (h : 2 * N.choose n < 2 ^ n.choose 2) : ¬ Forces N n n := by
  intro hF
  obtain ⟨c, hc⟩ := exists_good h
  rcases hF (graphOf c) with ⟨S, hS⟩ | ⟨T, hT⟩
  · refine hc S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.card_eq⟩) (Or.inl ?_)
    intro p hp
    rw [mem_pairs] at hp
    have hadj := graphOf_adj.mp (hS.isClique hp.1 hp.2.1 (ne_of_lt hp.2.2))
    rw [min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    exact hadj.2
  · refine hc T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT.card_eq⟩) (Or.inr ?_)
    intro p hp
    rw [mem_pairs] at hp
    have hadj := hT.isClique hp.1 hp.2.1 (ne_of_lt hp.2.2)
    rw [compl_adj, graphOf_adj] at hadj
    rw [min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    by_contra hcp
    exact hadj.2 ⟨hadj.1, by simpa using hcp⟩

/-! ## From the search to the bound -/

theorem fact_eq : ∀ n, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by rw [fact, Nat.factorial_succ, fact_eq n]

-- The search returns a value satisfying the predicate whenever its lower end does.
theorem bsearch_ok {n K : ℕ} :
    ∀ fuel lo hi, 2 * lo ^ n < K → 2 * (bsearch n K fuel lo hi) ^ n < K := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h; simpa [bsearch] using h
  | succ fuel ih =>
    intro lo hi h
    rw [bsearch]
    split_ifs with h1 h2
    · exact h
    · exact ih _ _ h2
    · exact ih _ _ h

theorem erdos_ok {n : ℕ} (hn : 1 ≤ n) :
    2 * (erdos n) ^ n < n.factorial * 2 ^ n.choose 2 := by
  have h0 : 2 * (0 : ℕ) ^ n < thr n := by
    rw [zero_pow (by omega), Nat.mul_zero, thr, fact_eq]
    positivity
  rw [Nat.choose_two_right, ← fact_eq]
  exact bsearch_ok (n + 1) 0 (2 ^ n) h0

-- Any `M` with `2 · M^n < n! · 2^C(n,2)` gives `f n ≥ M + 1`, since `n! · C(N,n) ≤ N^n`.
theorem main {n M : ℕ} (hn2 : 2 ≤ n) (hM : 2 * M ^ n < n.factorial * 2 ^ n.choose 2) :
    M + 1 ≤ f n := by
  have hn : nMin ≤ n := by simpa [nMin] using hn2
  refine le_f hn ?_
  intro N hN
  by_contra hcon
  have hNM : N ≤ M := by omega
  refine not_forces ?_ hN
  have h1 : N.choose n ≤ M.choose n := Nat.choose_le_choose n hNM
  have h2 : n.factorial * M.choose n ≤ M ^ n := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow M n
  have h3 : n.factorial * (2 * N.choose n) < n.factorial * 2 ^ n.choose 2 := by
    calc n.factorial * (2 * N.choose n) = 2 * (n.factorial * N.choose n) := by ring
      _ ≤ 2 * (n.factorial * M.choose n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ ≤ 2 * M ^ n := Nat.mul_le_mul_left _ h2
      _ < n.factorial * 2 ^ n.choose 2 := hM
  exact Nat.lt_of_mul_lt_mul_left h3

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v := by
  refine pin_lowerBoundHolds ?_
  intro n hn
  have hn2 : 2 ≤ n := by simpa [nMin] using hn
  exact main hn2 (erdos_ok (by omega))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V005.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V005.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V005.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 20) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V006
