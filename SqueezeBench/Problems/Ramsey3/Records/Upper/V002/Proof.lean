import SqueezeBench.Problems.Ramsey3.Records.Upper.V002.Def
import SqueezeBench.Problems.Ramsey3.Records.Upper.V001.Proof

/-! Record V002 for Ramsey3, upper direction, by trial claude-fable: the three obligations.

The mathematics is Shearer's bound for triangle-free graphs in its degree-sequence form
(J. B. Shearer, *A note on the independence number of triangle-free graphs, II*, J. Combin.
Theory Ser. B 53 (1991), 300–307): with `f 0 = 1` and `f d = (1 + (d² - d) f (d-1)) / (d² + 1)`,
every triangle-free graph has an independent set of size at least `Σ_v f (deg v)`.

The proof is an induction over vertex subsets `S` of a fixed graph. Deleting a vertex `v` and its
neighbourhood lowers the degree of each remaining `u` by the number `c u v` of common
neighbours, and by convexity of `f` this costs at most `c u v · del (deg u)` per vertex, where
`del d = f (d-1) - f d`. Averaging the resulting requirement over all `v ∈ S`, the double count
`Σ_{v ∉ N[u]} c u v = Σ_{w ∈ N(u)} (deg w - 1)` (triangle-freeness), the rearrangement inequality
for the decreasing `del`, and the recurrence in the form `(1 + d) f d - d (d - 1) del d = 1`
show that some `v` works.

In a graph with no independent `k`-set every degree is at most `k - 1`, so
`n · f (k-1) ≤ α ≤ k - 1`, and `⌊(k-1) / f (k-1)⌋ + 1` vertices force a triangle or a `K_k`. -/

namespace SqueezeBench.Ramsey3.Upper.V002

open Finset SimpleGraph SqueezeBench SqueezeBench.Ramsey

/-- Shearer's sequence as a rational: `sh 0 = 1`, `sh (d+1) = (1 + (d+1) d sh d) / ((d+1)² + 1)`. -/
def sh (d : ℕ) : ℚ := ((shearer d).1 : ℚ) / ((shearer d).2 : ℚ)

theorem shearer_pos (d : ℕ) : 0 < (shearer d).1 ∧ 0 < (shearer d).2 := by
  induction d with
  | zero => simp [shearer]
  | succ d ih =>
    simp only [shearer]
    constructor
    · exact Nat.add_pos_left ih.2 _
    · exact Nat.mul_pos (by omega) ih.2

theorem sh_zero : sh 0 = 1 := by simp [sh, shearer]

theorem sh_succ (d : ℕ) :
    sh (d + 1) = (1 + ((d : ℚ) + 1) * d * sh d) / (((d : ℚ) + 1) * (d + 1) + 1) := by
  have h1 : (0 : ℚ) < (shearer d).1 := by exact_mod_cast (shearer_pos d).1
  have h2 : (0 : ℚ) < (shearer d).2 := by exact_mod_cast (shearer_pos d).2
  unfold sh
  simp only [shearer]
  push_cast
  field_simp

/-- The recurrence, cleared of denominators. -/
theorem sh_rec (d : ℕ) :
    (((d : ℚ) + 1) * (d + 1) + 1) * sh (d + 1) = 1 + ((d : ℚ) + 1) * d * sh d := by
  rw [sh_succ]
  have : (((d : ℚ) + 1) * (d + 1) + 1) ≠ 0 := by positivity
  field_simp

/-- A crude lower bound, enough for monotonicity and convexity. -/
theorem sh_lower (d : ℕ) : 3 / (2 * (d : ℚ) + 5) ≤ sh d := by
  induction d with
  | zero => rw [sh_zero]; norm_num
  | succ d ih =>
    rw [sh_succ]
    have hd : (0 : ℚ) ≤ d := by positivity
    have h3 : (0 : ℚ) < 2 * (d : ℚ) + 5 := by positivity
    have key : 3 ≤ (2 * (d : ℚ) + 5) * sh d := by
      rwa [div_le_iff₀ h3, mul_comm] at ih
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [key, mul_nonneg hd hd, mul_nonneg hd (mul_nonneg hd hd)]

theorem sh_pos (d : ℕ) : 0 < sh d :=
  lt_of_lt_of_le (by positivity) (sh_lower d)

/-- `sh` is decreasing: `sh (d+1) ≤ sh d`. -/
theorem sh_succ_le (d : ℕ) : sh (d + 1) ≤ sh d := by
  have hrec := sh_rec d
  have hd : (0 : ℚ) ≤ d := by positivity
  have h3 : (0 : ℚ) < 2 * (d : ℚ) + 5 := by positivity
  have key : 3 ≤ (2 * (d : ℚ) + 5) * sh d := by
    have := sh_lower d
    rwa [div_le_iff₀ h3, mul_comm] at this
  nlinarith [sh_pos (d + 1), sh_pos d]

theorem sh_anti : Antitone sh := antitone_nat_of_succ_le sh_succ_le

/-- The backward difference `sh (d-1) - sh d`; it is `0` at `d = 0`. -/
def del (d : ℕ) : ℚ := sh (d - 1) - sh d

theorem del_zero : del 0 = 0 := by simp [del]

theorem del_succ (d : ℕ) : del (d + 1) = sh d - sh (d + 1) := by simp [del]

theorem del_nonneg (d : ℕ) : 0 ≤ del d := by
  cases d with
  | zero => simp [del_zero]
  | succ d => rw [del_succ]; linarith [sh_succ_le d]

/-- Convexity: the differences decrease from `d = 1` on. -/
theorem del_succ_succ_le (d : ℕ) : del (d + 2) ≤ del (d + 1) := by
  rw [del_succ, del_succ]
  have hd : (0 : ℚ) ≤ d := by positivity
  have h3 : (0 : ℚ) < 2 * (d : ℚ) + 5 := by positivity
  have key : 3 ≤ (2 * (d : ℚ) + 5) * sh d := by
    have := sh_lower d
    rwa [div_le_iff₀ h3, mul_comm] at this
  have h1 := sh_rec d
  have h2 := sh_rec (d + 1)
  push_cast at h2
  have hAC : (((d : ℚ) + 1) * (d + 1) + 1) * (((d : ℚ) + 1 + 1) * (d + 1 + 1) + 1) *
      (sh d + sh (d + 1 + 1) - 2 * sh (d + 1)) =
      (2 * (d : ℚ) ^ 2 + 10 * d + 10) * sh d - 3 * ((d : ℚ) + 2) := by
    linear_combination (((d : ℚ) + 1) * (d + 1) + 1) * h2 +
      (((d : ℚ) + 2) * (d + 1) - 2 * (((d : ℚ) + 2) * (d + 2) + 1)) * h1
  have hnn : 0 ≤ (2 * (d : ℚ) ^ 2 + 10 * d + 10) * sh d - 3 * ((d : ℚ) + 2) := by
    nlinarith [key, sh_pos d, hd]
  have hpos : 0 < (((d : ℚ) + 1) * (d + 1) + 1) * (((d : ℚ) + 1 + 1) * (d + 1 + 1) + 1) := by
    positivity
  have h4 : 0 ≤ sh d + sh (d + 1 + 1) - 2 * sh (d + 1) :=
    nonneg_of_mul_nonneg_right (by rw [hAC]; exact hnn) hpos
  linarith

theorem del_anti {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : del b ≤ del a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    refine le_trans ?_ ih
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    exact del_succ_succ_le c

/-- The tangent-line inequality: `sh (x - c) ≥ sh x + c · del x` for `c ≤ x`. -/
theorem sh_sub_ge (x : ℕ) : ∀ c, c ≤ x → sh x + c * del x ≤ sh (x - c) := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    have h1 := ih (by omega)
    have h2 : sh (x - (c + 1)) = sh (x - c) + del (x - c) := by
      rw [del]
      have : x - (c + 1) = x - c - 1 := by omega
      rw [this]; ring
    have h3 : del x ≤ del (x - c) := del_anti (by omega) (by omega)
    rw [h2]
    push_cast
    linarith

/-- The identity behind the averaging: `(1 + d) sh d - d (d - 1) del d = 1`. -/
theorem sh_identity (d : ℕ) : ((d : ℚ) + 1) * sh d - (d : ℚ) * ((d : ℚ) - 1) * del d = 1 := by
  cases d with
  | zero => simp [sh_zero, del_zero]
  | succ e =>
    rw [del_succ]
    have := sh_rec e
    push_cast
    nlinarith [this]

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbours of `u` inside `S`. -/
def nbr (S : Finset V) (u : V) : Finset V := S.filter (fun w => G.Adj u w)

/-- Non-neighbours of `v` inside `S`, other than `v` itself. -/
def non (S : Finset V) (v : V) : Finset V := S.filter (fun u => ¬ G.Adj v u ∧ u ≠ v)

/-- Common neighbours of `u` and `v` inside `S`. -/
def com (S : Finset V) (u v : V) : Finset V := S.filter (fun w => G.Adj u w ∧ G.Adj v w)

omit [DecidableEq V] in
theorem mem_nbr {S : Finset V} {u w : V} : w ∈ nbr G S u ↔ w ∈ S ∧ G.Adj u w := by
  simp [nbr]

theorem mem_non {S : Finset V} {v u : V} : u ∈ non G S v ↔ u ∈ S ∧ ¬ G.Adj v u ∧ u ≠ v := by
  simp [non]

omit [DecidableEq V] in
theorem mem_com {S : Finset V} {u v w : V} :
    w ∈ com G S u v ↔ w ∈ S ∧ G.Adj u w ∧ G.Adj v w := by
  simp [com]

omit [DecidableRel G.Adj] in
/-- Triangle-freeness, as a statement about three vertices. -/
theorem no_triangle (h : G.CliqueFree 3) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) :
    ¬ G.Adj a c := fun hac =>
  h {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

theorem non_ssubset {S : Finset V} {v : V} (hv : v ∈ S) : non G S v ⊂ S :=
  Finset.filter_ssubset.mpr ⟨v, hv, by simp⟩

theorem not_mem_non {S : Finset V} (v : V) : v ∉ non G S v := by simp [non]

/-- `S` splits into `v`, its neighbours and its non-neighbours. -/
theorem sum_split {S : Finset V} {v : V} (hv : v ∈ S) (g : V → ℚ) :
    ∑ u ∈ S, g u = g v + ∑ u ∈ nbr G S v, g u + ∑ u ∈ non G S v, g u := by
  have h1 := (Finset.sum_filter_add_sum_filter_not S (fun u => G.Adj v u) g).symm
  have h2 : S.filter (fun u => ¬ G.Adj v u) = insert v (non G S v) := by
    ext u
    simp only [non, mem_filter, mem_insert]
    constructor
    · rintro ⟨hu, hn⟩
      by_cases h : u = v
      · exact Or.inl h
      · exact Or.inr ⟨hu, hn, h⟩
    · rintro (rfl | ⟨hu, hn, _⟩)
      · exact ⟨hv, G.irrefl⟩
      · exact ⟨hu, hn⟩
  rw [h1, h2, Finset.sum_insert (not_mem_non G v)]
  simp only [nbr]
  ring

/-- Deleting `N[v]` lowers the degree of `u` by the number of common neighbours. -/
theorem card_nbr_non {S : Finset V} {v u : V} (hu : u ∈ non G S v) :
    (nbr G (non G S v) u).card + (com G S u v).card = (nbr G S u).card := by
  rw [mem_non] at hu
  have h := Finset.card_filter_add_card_filter_not (s := nbr G S u) (fun w => G.Adj v w)
  have e1 : (nbr G S u).filter (fun w => G.Adj v w) = com G S u v := by
    ext w; simp only [nbr, com, mem_filter]; tauto
  have e2 : (nbr G S u).filter (fun w => ¬ G.Adj v w) = nbr G (non G S v) u := by
    ext w
    simp only [nbr, non, mem_filter]
    constructor
    · rintro ⟨⟨hw, huw⟩, hvw⟩
      refine ⟨⟨hw, hvw, ?_⟩, huw⟩
      rintro rfl
      exact hu.2.1 ((G.adj_comm _ _).mp huw)
    · rintro ⟨⟨hw, hvw, _⟩, huw⟩
      exact ⟨⟨hw, huw⟩, hvw⟩
  rw [e1, e2] at h
  omega

/-- The walk count: `Σ_{x ∉ N[u]} |N(u) ∩ N(x)| + deg u = Σ_{w ∈ N(u)} deg w`, all inside `S`. -/
theorem count_walks (htf : G.CliqueFree 3) {S : Finset V} {u : V} (hu : u ∈ S) :
    ∑ x ∈ non G S u, (com G S u x).card + (nbr G S u).card = ∑ w ∈ nbr G S u, (nbr G S w).card := by
  have e1 : ∀ x, com G S u x = (nbr G S u).bipartiteAbove (fun x w => G.Adj x w) x := by
    intro x; ext w
    simp only [com, mem_filter, Finset.mem_bipartiteAbove, nbr]
    tauto
  have h2 := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := non G S u)
    (t := nbr G S u) (r := fun x w => G.Adj x w)
  have e3 : ∀ w ∈ nbr G S u,
      (nbr G S w).card = ((non G S u).bipartiteBelow (fun x w => G.Adj x w) w).card + 1 := by
    intro w hw
    rw [mem_nbr] at hw
    have hnot : u ∉ (non G S u).bipartiteBelow (fun x w => G.Adj x w) w := by
      simp [Finset.mem_bipartiteBelow, non]
    rw [← Finset.card_insert_of_notMem hnot]
    congr 1
    ext x
    simp only [nbr, mem_filter, mem_insert, Finset.mem_bipartiteBelow, non]
    constructor
    · rintro ⟨hx, hwx⟩
      by_cases hxu : x = u
      · exact Or.inl hxu
      · exact Or.inr ⟨⟨hx, no_triangle G htf hw.2 hwx, hxu⟩, (G.adj_comm _ _).mp hwx⟩
    · rintro (rfl | ⟨⟨hx, _, _⟩, hxw⟩)
      · exact ⟨hu, (G.adj_comm _ _).mp hw.2⟩
      · exact ⟨hx, (G.adj_comm _ _).mp hxw⟩
  rw [Finset.sum_congr rfl (fun x _ => by rw [e1 x]), h2, Finset.sum_congr rfl e3,
    Finset.sum_add_distrib]
  simp

omit [DecidableEq V] in
/-- `Σ_v Σ_{u ∈ N(v)} g u = Σ_u deg u · g u`. -/
theorem sum_nbr (S : Finset V) (g : V → ℚ) :
    ∑ v ∈ S, ∑ u ∈ nbr G S v, g u = ∑ u ∈ S, ((nbr G S u).card : ℚ) * g u := by
  simp only [nbr, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [G.adj_comm v u]
  split_ifs <;> simp

/-- Swapping the order of a sum over non-adjacent ordered pairs. -/
theorem sum_non (S : Finset V) (g : V → V → ℚ) :
    ∑ v ∈ S, ∑ u ∈ non G S v, g u v = ∑ u ∈ S, ∑ v ∈ non G S u, g u v := by
  simp only [non, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  exact if_congr (by rw [G.adj_comm, ne_comm]) rfl rfl

omit [DecidableEq V] in
/-- The rearrangement inequality: `del` is decreasing on positive degrees. -/
theorem rearrange (S : Finset V) :
    ∑ u ∈ S, del (nbr G S u).card * (((nbr G S u).card : ℚ) * (((nbr G S u).card : ℚ) - 1))
      ≤ ∑ u ∈ S, del (nbr G S u).card * ∑ w ∈ nbr G S u, (((nbr G S w).card : ℚ) - 1) := by
  have hL : ∑ u ∈ S, del (nbr G S u).card * (((nbr G S u).card : ℚ) * (((nbr G S u).card : ℚ) - 1))
      = ∑ u ∈ S, ∑ w ∈ S, (if G.Adj u w then del (nbr G S u).card * (((nbr G S u).card : ℚ) - 1)
          else 0) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_filter]
    simp only [nbr, Finset.sum_const, nsmul_eq_mul]
    ring
  have hR : ∑ u ∈ S, del (nbr G S u).card * ∑ w ∈ nbr G S u, (((nbr G S w).card : ℚ) - 1)
      = ∑ u ∈ S, ∑ w ∈ S, (if G.Adj u w then del (nbr G S u).card * (((nbr G S w).card : ℚ) - 1)
          else 0) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_filter, Finset.mul_sum]
    rfl
  have key : ∀ u ∈ S, ∀ w ∈ S,
      (if G.Adj u w then del (nbr G S u).card * (((nbr G S u).card : ℚ) - 1) else 0)
        + (if G.Adj w u then del (nbr G S w).card * (((nbr G S w).card : ℚ) - 1) else 0)
      ≤ (if G.Adj u w then del (nbr G S u).card * (((nbr G S w).card : ℚ) - 1) else 0)
        + (if G.Adj w u then del (nbr G S w).card * (((nbr G S u).card : ℚ) - 1) else 0) := by
    intro u hu w hw
    by_cases h : G.Adj u w
    · have h' : G.Adj w u := (G.adj_comm u w).mp h
      simp only [h, h', if_true]
      have hu1 : 1 ≤ (nbr G S u).card := Finset.card_pos.mpr ⟨w, (mem_nbr G).mpr ⟨hw, h⟩⟩
      have hw1 : 1 ≤ (nbr G S w).card := Finset.card_pos.mpr ⟨u, (mem_nbr G).mpr ⟨hu, h'⟩⟩
      rcases le_total (nbr G S u).card (nbr G S w).card with hle | hle
      · have hd := del_anti hu1 hle
        have hc : ((nbr G S u).card : ℚ) ≤ (nbr G S w).card := by exact_mod_cast hle
        nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hc)]
      · have hd := del_anti hw1 hle
        have hc : ((nbr G S w).card : ℚ) ≤ (nbr G S u).card := by exact_mod_cast hle
        nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hc)]
    · have h' : ¬ G.Adj w u := fun h' => h ((G.adj_comm w u).mp h')
      simp [h, h']
  have e1 : ∑ u ∈ S, ∑ w ∈ S, (if G.Adj u w then del (nbr G S u).card * (((nbr G S u).card : ℚ) - 1)
          else 0)
      = ∑ u ∈ S, ∑ w ∈ S, (if G.Adj w u then del (nbr G S w).card * (((nbr G S w).card : ℚ) - 1)
          else 0) := Finset.sum_comm
  have e2 : ∑ u ∈ S, ∑ w ∈ S, (if G.Adj u w then del (nbr G S u).card * (((nbr G S w).card : ℚ) - 1)
          else 0)
      = ∑ u ∈ S, ∑ w ∈ S, (if G.Adj w u then del (nbr G S w).card * (((nbr G S u).card : ℚ) - 1)
          else 0) := Finset.sum_comm
  have h2 : (∑ u ∈ S, ∑ w ∈ S, (if G.Adj u w then del (nbr G S u).card * (((nbr G S u).card : ℚ) - 1)
          else 0))
      + (∑ u ∈ S, ∑ w ∈ S, (if G.Adj w u then del (nbr G S w).card * (((nbr G S w).card : ℚ) - 1)
          else 0))
      ≤ (∑ u ∈ S, ∑ w ∈ S, (if G.Adj u w then del (nbr G S u).card * (((nbr G S w).card : ℚ) - 1)
          else 0))
      + (∑ u ∈ S, ∑ w ∈ S, (if G.Adj w u then del (nbr G S w).card * (((nbr G S u).card : ℚ) - 1)
          else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun u hu => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun w hw => key u hu w hw)
  linarith [hL, hR, e1, e2, h2]

/-- The averaging step: some vertex satisfies the local requirement. -/
theorem exists_good (htf : G.CliqueFree 3) {S : Finset V} (hS : S.Nonempty) :
    ∃ v ∈ S, sh (nbr G S v).card + ∑ u ∈ nbr G S v, sh (nbr G S u).card
      - ∑ u ∈ non G S v, ((com G S u v).card : ℚ) * del (nbr G S u).card ≤ 1 := by
  apply Finset.exists_le_of_sum_le hS
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_nbr, sum_non]
  have hc : ∀ u ∈ S, ∑ v ∈ non G S u, ((com G S u v).card : ℚ) * del (nbr G S u).card
      = del (nbr G S u).card * ∑ w ∈ nbr G S u, (((nbr G S w).card : ℚ) - 1) := by
    intro u hu
    have h' : (∑ v ∈ non G S u, ((com G S u v).card : ℚ)) + ((nbr G S u).card : ℚ)
        = ∑ w ∈ nbr G S u, ((nbr G S w).card : ℚ) := by exact_mod_cast count_walks G htf hu
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← h']
    ring
  rw [Finset.sum_congr rfl hc]
  have hre := rearrange G S
  have hid : ∀ u ∈ S, sh (nbr G S u).card + ((nbr G S u).card : ℚ) * sh (nbr G S u).card
      - del (nbr G S u).card * (((nbr G S u).card : ℚ) * (((nbr G S u).card : ℚ) - 1)) = 1 := by
    intro u _
    linear_combination sh_identity (nbr G S u).card
  have hsum : ∑ u ∈ S, (sh (nbr G S u).card + ((nbr G S u).card : ℚ) * sh (nbr G S u).card
      - del (nbr G S u).card * (((nbr G S u).card : ℚ) * (((nbr G S u).card : ℚ) - 1)))
      = ∑ u ∈ S, (1 : ℚ) := Finset.sum_congr rfl hid
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  linarith [hre, hsum]

/-- Shearer's bound, relative to a vertex subset `S` of a triangle-free graph. -/
theorem shearer_indep (htf : G.CliqueFree 3) (S : Finset V) :
    ∃ T ⊆ S, G.IsIndepSet (T : Set V) ∧ ∑ u ∈ S, sh (nbr G S u).card ≤ (T.card : ℚ) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    obtain ⟨v, hv, hgood⟩ := exists_good G htf hS
    obtain ⟨T', hT'W, hT'ind, hT'card⟩ := ih (non G S v) (non_ssubset G hv)
    have hvT' : v ∉ T' := fun h => not_mem_non G v (hT'W h)
    refine ⟨insert v T', ?_, ?_, ?_⟩
    · exact Finset.insert_subset hv (hT'W.trans (Finset.filter_subset _ _))
    · rw [Finset.coe_insert, isIndepSet_iff, Set.pairwise_insert]
      refine ⟨hT'ind, fun b hb _ => ?_⟩
      have hb' := (mem_non G).mp (hT'W hb)
      exact ⟨hb'.2.1, fun h => hb'.2.1 ((G.adj_comm b v).mp h)⟩
    · rw [Finset.card_insert_of_notMem hvT']
      push_cast
      have h1 : ∀ u ∈ non G S v, sh (nbr G S u).card
          + ((com G S u v).card : ℚ) * del (nbr G S u).card ≤ sh (nbr G (non G S v) u).card := by
        intro u hu
        have hcard := card_nbr_non G hu
        have := sh_sub_ge (nbr G S u).card (com G S u v).card (by omega)
        have e : (nbr G S u).card - (com G S u v).card = (nbr G (non G S v) u).card := by omega
        rw [e] at this
        exact this
      have h2 := Finset.sum_le_sum h1
      rw [Finset.sum_add_distrib] at h2
      rw [sum_split G hv]
      linarith [hgood, hT'card, h2]

/-- `v k` vertices force a triangle or an independent `k`-set. -/
theorem forcesOn_v (k : ℕ) (hk : 1 ≤ k) : ForcesOn (v k) 3 k := by
  intro V _ _ G hcard
  classical
  by_contra hcon
  obtain ⟨hS, hT⟩ := not_or.mp hcon
  have htf : G.CliqueFree 3 := not_exists.mp hS
  have hT' : ∀ T : Finset V, ¬ Gᶜ.IsNClique k T := not_exists.mp hT
  have hind : ∀ T : Finset V, G.IsIndepSet (T : Set V) → T.card ≤ k - 1 := by
    intro T hTind
    by_contra h
    obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq (show k ≤ T.card by omega)
    refine hT' T' ⟨?_, hT'card⟩
    rw [isClique_compl]
    exact hTind.mono (Finset.coe_subset.mpr hT'T)
  have hdeg : ∀ u, (nbr G univ u).card ≤ k - 1 := by
    intro u
    apply hind
    intro a ha b hb _ hadj
    rw [Finset.mem_coe, mem_nbr] at ha hb
    exact no_triangle G htf ha.2 hadj hb.2
  obtain ⟨T, _, hTind, hTsum⟩ := shearer_indep G htf univ
  have hTk : (T.card : ℚ) ≤ ((k - 1 : ℕ) : ℚ) := by exact_mod_cast hind T hTind
  have hsum : (Fintype.card V : ℚ) * sh (k - 1) ≤ ∑ u ∈ univ, sh (nbr G univ u).card := by
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun u _ => sh_anti (hdeg u))
  have hv : ((k - 1 : ℕ) : ℚ) < (v k : ℚ) * sh (k - 1) := by
    have hp : (0 : ℚ) < (shearer (k - 1)).1 := by exact_mod_cast (shearer_pos _).1
    have hq : (0 : ℚ) < (shearer (k - 1)).2 := by exact_mod_cast (shearer_pos _).2
    have h1 : (((k - 1) * (shearer (k - 1)).2 : ℕ) : ℚ) / ((shearer (k - 1)).1 : ℚ)
        < (v k : ℚ) := by
      have := Nat.lt_floor_add_one
        ((((k - 1) * (shearer (k - 1)).2 : ℕ) : ℚ) / ((shearer (k - 1)).1 : ℚ))
      rw [Nat.floor_div_eq_div] at this
      simpa [v] using this
    have h2 : (((k - 1) * (shearer (k - 1)).2 : ℕ) : ℚ) / ((shearer (k - 1)).1 : ℚ) * sh (k - 1)
        = ((k - 1 : ℕ) : ℚ) := by
      unfold sh
      push_cast
      field_simp
    rw [← h2]
    exact mul_lt_mul_of_pos_right h1 (sh_pos _)
  have hcard' : (v k : ℚ) ≤ Fintype.card V := by exact_mod_cast hcard
  have h5 : (v k : ℚ) * sh (k - 1) ≤ (Fintype.card V : ℚ) * sh (k - 1) :=
    mul_le_mul_of_nonneg_right hcard' (le_of_lt (sh_pos _))
  linarith [hv, h5, hsum, hTsum, hTk]

theorem v_valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f v := by
  intro k
  rcases Nat.lt_or_ge k SqueezeBench.Ramsey3.nMin with h | h
  · rw [SqueezeBench.Ramsey3.f, if_pos h]
    exact Nat.zero_le _
  · have hk : 1 ≤ k := le_trans (by decide) h
    exact SqueezeBench.Ramsey3.f_le_of_forces h (Ramsey.forces_of_forcesOn (forcesOn_v k hk))


theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Ramsey3.f record :=
  SqueezeBench.minWith_valid SqueezeBench.Ramsey3.Upper.V001.valid v_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Ramsey3.Upper.V001.record record :=
  SqueezeBench.minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Ramsey3.nMin SqueezeBench.Ramsey3.Upper.V001.record record :=
  SqueezeBench.minWith_strict (nMin := SqueezeBench.Ramsey3.nMin) (n₀ := 10) (by decide) (by decide)

end SqueezeBench.Ramsey3.Upper.V002
