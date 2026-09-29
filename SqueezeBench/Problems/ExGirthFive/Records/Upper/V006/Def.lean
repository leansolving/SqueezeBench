import SqueezeBench.Problems.ExGirthFive.Records.Upper.V005.Def

/-! Record V006 for ExGirthFive, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Upper/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Upper.V006

-- A certificate is five lines `x ↦ (S·x + I)/Q` with `S, I ∈ ℕ`; `ψ` is their pointwise
-- minimum, a concave nondecreasing function. `Proof.lean` shows that for any such `ψ` and
-- any `Λ` with `2·d·ψ(N/d) + Q·d ≤ 2·d·ψ(d) + Λ` for every degree `d ≤ N = n - 1`, every
-- graph of girth `≥ 5` has `2·Q·m ≤ n·Λ`. The record computes the least such `Λ` itself.
abbrev Lines := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

-- `Q·ℓ(d)` for the line `ℓ = (S, I)` at the integer `d`.
def lineD (l : ℕ × ℕ) (d : ℕ) : ℕ := l.1 * d + l.2

-- `Q·d·ℓ(N/d)` for the line `ℓ = (S, I)`.
def lineN (l : ℕ × ℕ) (N d : ℕ) : ℕ := l.1 * N + l.2 * d

-- `Q·ψ(d)`, the minimum of the five lines at `d`.
def psiD (L : Lines) (d : ℕ) : ℕ :=
  min (lineD L.1 d) (min (lineD L.2.1 d) (min (lineD L.2.2.1 d)
    (min (lineD L.2.2.2.1 d) (lineD L.2.2.2.2 d))))

-- `Q·d·ψ(N/d)`, the minimum of the five lines at `N/d`, times `d`.
def psiN (L : Lines) (N d : ℕ) : ℕ :=
  min (lineN L.1 N d) (min (lineN L.2.1 N d) (min (lineN L.2.2.1 N d)
    (min (lineN L.2.2.2.1 N d) (lineN L.2.2.2.2 N d))))

-- What the degree `d` demands of `Λ`: `2·d·ψ(N/d) + Q·d − 2·d·ψ(d)` (truncated).
def term (L : Lines) (Q N d : ℕ) : ℕ := (2 * psiN L N d + Q * d) - 2 * (d * psiD L d)

-- The maximum of `term` over the degrees `0, …, D`.
def lamAux (L : Lines) (Q N : ℕ) : ℕ → ℕ
  | 0 => term L Q N 0
  | d + 1 => max (term L Q N (d + 1)) (lamAux L Q N d)

-- The bound `⌊n·Λ/(2Q)⌋` certified by the lines `L`; `C(n,2)` if the scale `Q` is `0`.
def certBound (L : Lines) (Q n : ℕ) : ℕ :=
  if Q = 0 then n * (n - 1) / 2 else n * lamAux L Q (n - 1) (n - 1) / (2 * Q)

-- The five lines through the breakpoints `q - 1, q, q + 1, q + 2` with slopes
-- `S₀ ≥ S₁ ≥ S₂ ≥ S₃ ≥ 0` (all over `Q`), flat beyond `q + 2`.
def mkLines (q S₀ S₁ S₂ S₃ : ℕ) : Lines :=
  ((S₀, 0), (S₁, (S₀ - S₁) * (q - 1)),
    (S₂, (S₀ - S₁) * (q - 1) + (S₁ - S₂) * q),
    (S₃, (S₀ - S₁) * (q - 1) + (S₁ - S₂) * q + (S₂ - S₃) * (q + 1)),
    (0, (S₀ - S₁) * (q - 1) + (S₁ - S₂) * q + (S₂ - S₃) * (q + 1) + S₃ * (q + 2)))

-- Candidate A (the optimum when `q` is small, `2 ≤ ρ < q - 2`): with
-- `D' = (q - 1) + ρ(3q - 2 - ρ)` and `c = q - 2 - ρ`, the slopes are
-- `s₀ = (q - 4 + 3ρ(q - 3 - ρ))/(2D'c)`, `s₁ = (ρ + 1)/D'`, `s₂ = (ρ - 1)/(2D')`, `s₃ = 0`.
def boundA (n : ℕ) : ℕ :=
  let N := n - 1
  let q := Nat.sqrt N
  let ρ := N - q * q
  let D' := (q - 1) + ρ * (3 * q - 2 - ρ)
  let c := q - 2 - ρ
  certBound (mkLines q (q - 4 + 3 * ρ * (q - 3 - ρ)) (2 * (ρ + 1) * c) ((ρ - 1) * c) 0)
    (2 * D' * c) n

-- Candidate B (the optimum when `q` is large): the solution of the five tight demands at
-- the degrees `q - 2, …, q + 2`, over the common denominator `2·Den`.
def boundB (n : ℕ) : ℕ :=
  let N := n - 1
  let q := Nat.sqrt N
  let ρ := N - q * q
  let Den := (5 * q * q * ρ * ρ + 15 * q * q * ρ + 4 * q * q + ρ * ρ * ρ * ρ + 11 * ρ * ρ * ρ
      + 38 * ρ * ρ + 44 * ρ + 16) - (6 * q * ρ * ρ * ρ + 30 * q * ρ * ρ + 52 * q * ρ + 16 * q)
  certBound (mkLines q
      (4 * ((q * ρ * ρ + 6 * q * ρ + 2 * q) - (ρ * ρ * ρ + 7 * ρ * ρ + 10 * ρ + 4)))
      (3 * (ρ + 1) * ((q * ρ + 4 * q) - (ρ * ρ + 4 * ρ + 8)))
      (2 * (ρ - 2) * ((q * ρ + 2 * q) - (ρ * ρ + 3 * ρ + 4)))
      ((q * ρ * ρ + 5 * ρ * ρ + 20 * ρ + 8) - (9 * q * ρ + 4 * q + ρ * ρ * ρ)))
    (2 * Den) n

def v : SqueezeBench.BoundFn := fun n => min (boundA n) (boundB n)

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.ExGirthFive.Upper.V005.record v

end SqueezeBench.ExGirthFive.Upper.V006
