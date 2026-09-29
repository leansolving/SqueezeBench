import SqueezeBench.Problems.CapSet.Records.Upper.V006.Def

/-! Record V007 for CapSet, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/CapSet/Upper/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.CapSet.Upper.V007

/-- Digit `k` of `P` in base `B`. With `B = 3ⁿ + 1` and `P = (1 + B + B²)ⁿ`, digit `k` is the
number of monomials `x₁^{a₁} ⋯ xₙ^{aₙ}` with `aᵢ ≤ 2` and `∑ aᵢ = k`: the coefficients of
`(1 + x + x²)ⁿ` are at most `3ⁿ`, so they do not carry. -/
def digit (P B k : ℕ) : ℕ := P / B ^ k % B

/-- `digit 0 + ⋯ + digit d`: the number `m_d` of monomials of degree at most `d`. -/
def msum (P B : ℕ) : ℕ → ℕ
  | 0 => digit P B 0
  | d + 1 => msum P B d + digit P B (d + 1)

/-- The Ellenberg–Gijswijt bound with parameter `d`: `3ⁿ − m_d + 2 m_{⌊d/2⌋}`. -/
def eg (n P B d : ℕ) : ℕ := 3 ^ n + 2 * msum P B (d / 2) - msum P B d

/-- The minimum of `eg` over the window `D - 2 ≤ d ≤ D + 2`, which contains the optimal
degree when `D = ⌊4n/3⌋`. -/
def egWin (n P B D : ℕ) : ℕ :=
  min (min (eg n P B (D - 2)) (eg n P B (D - 1)))
    (min (eg n P B D) (min (eg n P B (D + 1)) (eg n P B (D + 2))))

/-- The Ellenberg–Gijswijt bound, `min_d (3ⁿ − m_d + 2 m_{⌊d/2⌋})` over `d` near `4n/3`.
Everything is a handful of big-number operations, so the kernel evaluates it in under a
hundred heartbeats at every `n ≤ 100`. -/
def egBound (n : ℕ) : ℕ :=
  egWin n ((1 + (3 ^ n + 1) + (3 ^ n + 1) ^ 2) ^ n) (3 ^ n + 1) (4 * n / 3)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.CapSet.Upper.V006.record egBound

end SqueezeBench.CapSet.Upper.V007
