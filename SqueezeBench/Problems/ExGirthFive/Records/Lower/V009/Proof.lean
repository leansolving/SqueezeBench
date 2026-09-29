import SqueezeBench.Problems.ExGirthFive.Records.Lower.V009.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V008.Proof

/-! Record V009 for ExGirthFive, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V009.lean`.

Two additions to V008, both through its `subplane_le`. (1) A bound of order `n^{3/2}` valid for
*every* `n`, not only up to the end of a prime table: Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`) supplies a prime `p ∈ (q, 2q]` for `q = ⌊√(n/2)⌋`, and the
sub-plane with `⌊n/(4q)⌋` slope classes and `⌊n/2⌋` points fits into `n` vertices for any such
`p`, so the record need not know `p`. The square root is a fuel-based binary search of which only
the upper bracket `n/2 < (q+1)²` is proved; that is all validity needs. (2) The leftover of the
table construction now tries both integer neighbours of the balanced number of slope classes. -/

namespace SqueezeBench.ExGirthFive.Lower.V009

open SqueezeBench SqueezeBench.ExGirthFive SqueezeBench.ExGirthFive.Lower.V008

-- The search keeps `x < (hi+1)²` and returns `hi`.
theorem sqrtAux_spec (x : ℕ) : ∀ (fuel lo hi : ℕ), x < (hi + 1) * (hi + 1) →
    x < (sqrtAux x fuel lo hi + 1) * (sqrtAux x fuel lo hi + 1) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h; simpa [sqrtAux] using h
  | succ fuel ih =>
    intro lo hi h
    simp only [sqrtAux]
    split_ifs with h1 h2
    · exact h
    · exact ih _ _ h
    · apply ih
      have hmid : 1 ≤ (lo + hi + 1) / 2 := by omega
      rw [Nat.sub_add_cancel hmid]
      exact Nat.lt_of_not_le h2

theorem sqrtUp_spec (x : ℕ) : x < (sqrtUp x + 1) * (sqrtUp x + 1) :=
  sqrtAux_spec x x 0 x (by nlinarith)

-- Bertrand's prime `p ∈ (q, 2q]` carries `⌊n/(4q)⌋ ≤ p` classes and `⌊n/2⌋ ≤ p²` points.
theorem tail_le (n : ℕ) : tail n ≤ f n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n / 2 = 0 := by omega
    simp [tail, this]
  set q := sqrtUp (n / 2) with hq
  have hspec : n / 2 < (q + 1) * (q + 1) := sqrtUp_spec (n / 2)
  have hq1 : 1 ≤ q := by
    by_contra h0
    have : q = 0 := by omega
    rw [this] at hspec
    omega
  obtain ⟨p, hp, hqp, hp2q⟩ := Nat.exists_prime_lt_and_le_two_mul q (by omega)
  have h4q : 0 < 4 * q := by omega
  have hdiv := Nat.div_add_mod n 2
  have hdiv2 := Nat.div_mul_le_self n (4 * q)
  have hmod : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hqq : 1 * 1 ≤ q * q := Nat.mul_le_mul hq1 hq1
  have hs : n / (4 * q) ≤ p := by
    have : n / (4 * q) < q + 1 := by
      rw [Nat.div_lt_iff_lt_mul h4q]
      nlinarith
    omega
  have hm : n / 2 ≤ p * p := by nlinarith
  have h3 : n / (4 * q) * p ≤ n / (4 * q) * (2 * q) := Nat.mul_le_mul_left _ hp2q
  have h4 : 2 * (n / (4 * q) * (2 * q)) = n / (4 * q) * (4 * q) := by ring
  have hsum : 0 * (2 * p * p) + (n / (4 * q) * p + n / 2) ≤ n := by omega
  have := subplane_le p hp 0 (n / (4 * q)) (n / 2) n hs hm hsum
  simpa [tail] using this

-- A candidate with `s ≤ p` classes on `r` leftover vertices after `k` full planes.
theorem cand_le (p n k r s : ℕ) (hp : p.Prime) (hs : s ≤ p) (hkr : k * (2 * p * p) + r ≤ n) :
    k * (p * p * p) + cand p r s ≤ f n := by
  by_cases hc : r < s * p
  · have : cand p r s = 0 := by simp [cand, Nat.sub_eq_zero_of_le hc.le]
    rw [this]
    exact subplane_le p hp k 0 0 n (Nat.zero_le _) (Nat.zero_le _)
      (by simpa using le_trans (Nat.le_add_right _ _) hkr)
  · rw [not_lt] at hc
    refine subplane_le p hp k s (min (r - s * p) (p * p)) n hs (min_le_right _ _) ?_
    have : s * p + min (r - s * p) (p * p) ≤ r := by
      have := min_le_left (r - s * p) (p * p)
      omega
    omega

theorem blk2_le (p n : ℕ) (hp : p.Prime) : blk2 p n ≤ f n := by
  have hp0 : 0 < p := hp.pos
  have hpp : 0 < 2 * p * p := by positivity
  have hr : n % (2 * p * p) < 2 * p * p := Nat.mod_lt _ hpp
  have hdiv := Nat.div_add_mod n (2 * p * p)
  have hkr : n / (2 * p * p) * (2 * p * p) + n % (2 * p * p) ≤ n := by
    rw [mul_comm]; exact hdiv.le
  have hs0 : n % (2 * p * p) / (2 * p) + 1 ≤ p := by
    have : n % (2 * p * p) / (2 * p) < p := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      nlinarith
    omega
  have h1 := cand_le p n (n / (2 * p * p)) (n % (2 * p * p)) (n % (2 * p * p) / (2 * p)) hp
    (by omega) hkr
  have h2 := cand_le p n (n / (2 * p * p)) (n % (2 * p * p)) (n % (2 * p * p) / (2 * p) + 1) hp
    hs0 hkr
  calc blk2 p n = n / (2 * p * p) * (p * p * p) + part2 p (n % (2 * p * p)) := by
        rw [blk2, mul_comm]
    _ ≤ f n := by
        rw [part2]
        rcases le_total (cand p (n % (2 * p * p)) (n % (2 * p * p) / (2 * p)))
          (cand p (n % (2 * p * p)) (n % (2 * p * p) / (2 * p) + 1)) with h | h
        · rw [max_eq_right h]; exact h2
        · rw [max_eq_left h]; exact h1

theorem blocks2_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f blocks2 := by
  intro n
  have h : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) →
      (l.map fun p => blk2 p n).foldr max 0 ≤ f n := by
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons c t ih =>
        exact max_le (blk2_le c n (hl c (by simp))) (ih fun q hq => hl q (by simp [hq]))
  exact h primes primes_prime

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V008.valid
    fun n => max_le (blocks2_valid n) (tail_le n)

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V008.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V008.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin)
    (n₀ := 100000000000000000000) (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V009
