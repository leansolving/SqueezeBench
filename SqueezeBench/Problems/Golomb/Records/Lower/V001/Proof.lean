import SqueezeBench.Problems.Golomb.Records.Lower.V001.Def
import SqueezeBench.Problems.Golomb.Records.Lower.V000.Proof

/-!
# Golomb lower-bound record V001 — validity

Slide a window of length `v + 1` along `[0, L]`. Let `cnt s` be the number of marks in the
window ending at `s`. Summing over the `L + v + 1` windows that can contain a mark,

* `∑ cnt s = m * (v + 1)`, each mark lying in exactly `v + 1` windows;
* `∑ cnt s * (cnt s - 1) ≤ v * (v + 1)`, because a pair of marks at distance `d` lies in
  `v + 1 - d` common windows and the Sidon property makes the distances distinct;
* `2 * q * n ≤ n * (n - 1) + q * (q + 1)` for every `n`, the tangent line to `n(n-1)` at the
  integer `q` — it is `(n - q) * (n - q - 1) ≥ 0`.

Together `2 * q * (v + 1) * m ≤ (L + v + 1) * q * (q + 1) + v * (v + 1)`, which is the master
inequality; solving it for `L` gives the record. With `q ≈ √m` and `v + 1 ≈ q m − q(q+1)/2`
the bound is `m² − 2 m^{3/2} + O(m)`.

The `spread` of a pair and its injectivity are V000's; see `based-on`.
-/

namespace SqueezeBench.Golomb.Lower.V001

open SqueezeBench Finset
open SqueezeBench.Golomb.Lower.V000 (spread spread_pair exists_pair)

/-! ## Elementary arithmetic -/

theorem div_le_of_mul_le {A C X : ℕ} (hC : 0 < C) (h : A ≤ X * C) : A / C ≤ X :=
  Nat.le_of_mul_le_mul_right (le_trans (Nat.div_mul_le_self A C) h) hC

theorem two_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rcases n with _ | k
  · simp
  · rw [Nat.choose_two_right]
    simp only [Nat.succ_sub_one]
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self k
    have h : (k + 1) * k = r + r := by rw [mul_comm]; exact hr
    rw [h]
    omega

/-- The tangent line to `n * (n - 1)` at the integer `q`; it is `(n - q) * (n - q - 1) ≥ 0`. -/
theorem tangent (n q : ℕ) : 2 * q * n ≤ n * (n - 1) + q * (q + 1) := by
  rcases n with _ | k
  · simp
  · simp only [Nat.succ_sub_one]
    rcases Nat.le_total q k with h | h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      nlinarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      have hii : i ≤ i * i := by
        rcases i with _ | i'
        · simp
        · nlinarith
      nlinarith

/-- `∑_{d = 1}^{v} (v + 1 - d)` is the triangular number. -/
theorem tri (v : ℕ) : 2 * ∑ d ∈ Finset.Icc 1 v, (v + 1 - d) = v * (v + 1) := by
  have h0 : Finset.Icc 1 v = Finset.Ico 1 (v + 1) := (Finset.Ico_add_one_right_eq_Icc 1 v).symm
  have h1 : ∑ d ∈ Finset.Icc 1 v, (v + 1 - d) = ∑ i ∈ range v, (v - i) := by
    rw [h0, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) ?_
    intro i hi
    simp only [mem_range] at hi
    omega
  have h2 : ∑ i ∈ range v, (v - i) = ∑ i ∈ range v, (i + 1) := by
    rw [← Finset.sum_range_reflect (fun j => j + 1) v]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp only [mem_range] at hi
    omega
  have h4 : ∑ i ∈ range v, (i + 1) = (∑ i ∈ range v, i) + v := by
    rw [Finset.sum_add_distrib, Finset.sum_const, card_range, smul_eq_mul, mul_one]
  rcases v with _ | k
  · simp
  · have h3 : (∑ i ∈ range (k + 1), i) * 2 = (k + 1) * k := by
      simpa using Finset.sum_range_id_mul_two (k + 1)
    have e : (k + 1) * (k + 1 + 1) = (k + 1) * k + 2 * (k + 1) := by ring
    rw [h1, h2, h4, e]
    omega

/-! ## Windows -/

/-- The marks of `S` in the window `[s - v, s]`. -/
def win (S : Finset ℕ) (v s : ℕ) : Finset ℕ := S.filter (fun a => a ≤ s ∧ s ≤ a + v)

/-- How many marks the window ending at `s` holds. -/
def cnt (S : Finset ℕ) (v s : ℕ) : ℕ := (win S v s).card

theorem win_subset (S : Finset ℕ) (v s : ℕ) : win S v s ⊆ S := filter_subset _ _

theorem mem_win {S : Finset ℕ} {v s a : ℕ} :
    a ∈ win S v s ↔ a ∈ S ∧ a ≤ s ∧ s ≤ a + v := by
  simp [win, mem_filter, and_assoc]

/-- Each mark lies in exactly `v + 1` of the windows. -/
theorem sum_cnt {S : Finset ℕ} {L v : ℕ} (hS : ∀ a ∈ S, a ≤ L) :
    ∑ s ∈ range (L + v + 1), cnt S v s = S.card * (v + 1) := by
  have key : ∀ s, cnt S v s = ∑ a ∈ S, if a ≤ s ∧ s ≤ a + v then 1 else 0 := by
    intro s; rw [cnt, win, card_filter]
  simp only [key]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (g := fun _ => v + 1) ?_]
  · rw [Finset.sum_const, smul_eq_mul]
  · intro a ha
    have hla := hS a ha
    have hfe : ((range (L + v + 1)).filter (fun s => a ≤ s ∧ s ≤ a + v)) = Finset.Icc a (a + v) := by
      ext s
      simp only [mem_filter, mem_range, mem_Icc]
      omega
    rw [← Finset.sum_filter, hfe, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
    omega

/-- Two marks at distance `d` lie together in `v + 1 - d` windows. -/
theorem sum_choose_eq {S : Finset ℕ} {L v : ℕ} (hS : ∀ a ∈ S, a ≤ L) :
    ∑ s ∈ range (L + v + 1), (cnt S v s).choose 2
      = ∑ P ∈ S.powersetCard 2, ((v + 1) - spread P) := by
  have key : ∀ s, (cnt S v s).choose 2
      = ∑ P ∈ S.powersetCard 2, if P ⊆ win S v s then 1 else 0 := by
    intro s
    rw [← card_filter, cnt, ← card_powersetCard]
    congr 1
    ext P
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.trans (win_subset S v s), h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro P hP
  rw [mem_powersetCard] at hP
  obtain ⟨a, b, hab, rfl⟩ := exists_pair hP.2
  have ha : a ∈ S := hP.1 (by simp)
  have hb : b ∈ S := hP.1 (by simp)
  have hla := hS a ha
  have hlb := hS b hb
  have hfe : ((range (L + v + 1)).filter (fun s => ({a, b} : Finset ℕ) ⊆ win S v s))
      = Finset.Icc b (a + v) := by
    ext s
    simp only [mem_filter, mem_range, mem_Icc, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, mem_win]
    constructor
    · rintro ⟨-, ⟨-, h1, h2⟩, -, h3, h4⟩; omega
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, ⟨ha, by omega, by omega⟩, hb, by omega, by omega⟩
  rw [← Finset.sum_filter, hfe, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc,
    spread_pair hab]
  omega

/-! ## The Sidon property -/

theorem spread_injOn {S : Finset ℕ} (hsid : IsSidon S) :
    ∀ T ∈ S.powersetCard 2, ∀ T' ∈ S.powersetCard 2, spread T = spread T' → T = T' := by
  intro T hT T' hT' heq
  rw [mem_powersetCard] at hT hT'
  obtain ⟨a, b, hab, rfl⟩ := exists_pair hT.2
  obtain ⟨c, d, hcd, rfl⟩ := exists_pair hT'.2
  have ha : a ∈ S := hT.1 (by simp)
  have hb : b ∈ S := hT.1 (by simp)
  have hc : c ∈ S := hT'.1 (by simp)
  have hd : d ∈ S := hT'.1 (by simp)
  rw [spread_pair hab, spread_pair hcd] at heq
  have hsum : b + c = a + d := by omega
  rcases hsid b hb c hc a ha d hd hsum with ⟨h1, _⟩ | ⟨h1, h2⟩
  · omega
  · rw [h1, h2]

theorem one_le_spread {S : Finset ℕ} {P : Finset ℕ} (hP : P ∈ S.powersetCard 2) :
    1 ≤ spread P := by
  rw [mem_powersetCard] at hP
  obtain ⟨a, b, hab, rfl⟩ := exists_pair hP.2
  rw [spread_pair hab]
  omega

/-- The distances are distinct, so the windows hold at most `v (v+1) / 2` pairs in total. -/
theorem sum_spread_le {S : Finset ℕ} (v : ℕ) (hsid : IsSidon S) :
    2 * ∑ P ∈ S.powersetCard 2, ((v + 1) - spread P) ≤ v * (v + 1) := by
  classical
  have h1 : ∑ P ∈ (S.powersetCard 2).filter (fun P => spread P ≤ v), ((v + 1) - spread P)
      = ∑ P ∈ S.powersetCard 2, ((v + 1) - spread P) := by
    refine Finset.sum_subset (filter_subset _ _) ?_
    intro P hP hPn
    rw [mem_filter] at hPn
    have : ¬ spread P ≤ v := fun h => hPn ⟨hP, h⟩
    omega
  have hinj : ∀ T ∈ (S.powersetCard 2).filter (fun P => spread P ≤ v),
      ∀ T' ∈ (S.powersetCard 2).filter (fun P => spread P ≤ v), spread T = spread T' → T = T' := by
    intro T hT T' hT' h
    rw [mem_filter] at hT hT'
    exact spread_injOn hsid T hT.1 T' hT'.1 h
  have h2 : ∑ d ∈ ((S.powersetCard 2).filter (fun P => spread P ≤ v)).image spread,
      ((v + 1) - d) = ∑ P ∈ (S.powersetCard 2).filter (fun P => spread P ≤ v),
      ((v + 1) - spread P) := Finset.sum_image hinj
  have h3 : ((S.powersetCard 2).filter (fun P => spread P ≤ v)).image spread ⊆ Finset.Icc 1 v := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨P, hP, rfl⟩ := hd
    rw [mem_filter] at hP
    rw [mem_Icc]
    exact ⟨one_le_spread hP.1, hP.2⟩
  have h4 := Finset.sum_le_sum_of_subset (f := fun d => (v + 1) - d) h3
  have h5 := tri v
  omega

/-! ## The master inequality -/

theorem master {m L : ℕ} (hL : L ∈ RulerLengths m) (q v : ℕ) :
    2 * q * (v + 1) * m ≤ (L + v + 1) * (q * (q + 1)) + v * (v + 1) := by
  obtain ⟨S, hsub, hcard, hsid, _⟩ := hL
  have hS : ∀ a ∈ S, a ≤ L := by
    intro a ha
    have := hsub ha
    rw [mem_range] at this
    omega
  have e1 : ∑ s ∈ range (L + v + 1), cnt S v s = m * (v + 1) := by
    rw [sum_cnt hS, hcard]
  have e2 : 2 * ∑ s ∈ range (L + v + 1), (cnt S v s).choose 2 ≤ v * (v + 1) := by
    rw [sum_choose_eq hS]
    exact sum_spread_le v hsid
  have e3 : ∀ s ∈ range (L + v + 1),
      2 * q * cnt S v s ≤ 2 * (cnt S v s).choose 2 + q * (q + 1) := by
    intro s _
    have h := tangent (cnt S v s) q
    have hc := two_choose_two (cnt S v s)
    omega
  have e4 := Finset.sum_le_sum e3
  rw [← Finset.mul_sum, e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    card_range, smul_eq_mul] at e4
  have heq : 2 * q * (v + 1) * m = 2 * q * (m * (v + 1)) := by ring
  rw [heq]
  omega

/-! ## The obligations -/

theorem w_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f w := by
  refine pin_lowerBoundHolds ?_
  intro m hm
  refine le_f hm ?_
  intro L hL
  have hq : 1 ≤ qOf m := le_max_left 1 _
  have hqq : 0 < qOf m * (qOf m + 1) := Nat.mul_pos hq (by omega)
  have hmas := master hL (qOf m) (vOf m)
  have key : 2 * qOf m * (vOf m + 1) * m - vOf m * (vOf m + 1)
      ≤ (L + vOf m + 1) * (qOf m * (qOf m + 1)) := by omega
  have h1 : (2 * qOf m * (vOf m + 1) * m - vOf m * (vOf m + 1)) / (qOf m * (qOf m + 1))
      ≤ L + vOf m + 1 := div_le_of_mul_le hqq key
  have h2 : wRaw m
      = (2 * qOf m * (vOf m + 1) * m - vOf m * (vOf m + 1)) / (qOf m * (qOf m + 1))
        - (vOf m + 1) := rfl
  rw [h2]
  omega

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Golomb.f record :=
  maxWith_valid SqueezeBench.Golomb.Lower.V000.valid w_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Golomb.Lower.V000.record record :=
  maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Lower.V000.record record :=
  maxWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 11) (by decide) (by decide)

end SqueezeBench.Golomb.Lower.V001
