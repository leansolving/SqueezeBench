import SqueezeBench.Problems.Golomb.Records.Upper.V002.Def
import SqueezeBench.Problems.Golomb.Records.Upper.V001.Proof

/-!
# Golomb upper-bound record V002 — validity

V001 bounded the length of the Erdős–Turán ruler `aₖ = 2pk + (k² mod p)` by feeding it
Bertrand's worst-case prime `p ≤ 2m`. Here the record carries the least prime `p > m`
itself, so the bound is the ruler's actual length `2p(m-1) + ((m-1)² mod p)`.

The ruler and its Sidon property are V001's `etRuler_mem`, reused verbatim; the new work is
that `nextPrime m` really is a prime above `m`. That is `List.find?_some` for the value
found, and Bertrand's postulate to rule out the `none` branch: the prime `p ∈ (m, 2m]` it
supplies sits at offset `p - m - 1 ≤ m` in the searched range.
-/

namespace SqueezeBench.Golomb.Upper.V002

open SqueezeBench

theorem nextPrime_spec {m : ℕ} (hm : 1 ≤ m) : (nextPrime m).Prime ∧ m < nextPrime m := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  rw [nextPrime]
  split
  next d heq =>
    have hd := List.find?_some heq
    exact ⟨of_decide_eq_true hd, by omega⟩
  next heq =>
    exfalso
    have hmem : p - m - 1 ∈ List.range (m + 1) := by
      rw [List.mem_range]; omega
    have hnone := List.find?_eq_none.mp heq _ hmem
    have hval : m + 1 + (p - m - 1) = p := by omega
    rw [hval] at hnone
    exact absurd (decide_eq_true hp) hnone

theorem etLen_valid : UpperBoundHolds f etLen := by
  intro m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [f, nMin]
    · have h := f_le_binRuler 1 (by simp)
      have hz : etLen 1 = 0 := by decide +kernel
      rw [hz]
      simpa using h
  · obtain ⟨hp, hlt⟩ := nextPrime_spec (m := m) (by omega)
    have hp2 : nextPrime m ≠ 2 := by omega
    exact f_le_of_mem (by simp only [nMin_eq]; omega)
      (V001.etRuler_mem hp hp2 (by omega) (le_of_lt hlt))

theorem valid : SqueezeBench.UpperBoundHolds SqueezeBench.Golomb.f record :=
  minWith_valid V001.valid etLen_valid

theorem improves : SqueezeBench.ImprovesUpper SqueezeBench.Golomb.Upper.V001.record record :=
  minWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesUpper SqueezeBench.Golomb.nMin SqueezeBench.Golomb.Upper.V001.record record :=
  minWith_strict (nMin := SqueezeBench.Golomb.nMin) (n₀ := 10) (by decide) (by decide +kernel)

end SqueezeBench.Golomb.Upper.V002
