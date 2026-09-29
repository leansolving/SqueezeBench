import SqueezeBench.Problems.RuzsaSzemeredi.Records.Upper.V007.Def

/-! Record V008 for RuzsaSzemeredi, upper direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/RuzsaSzemeredi/Upper/V008.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.RuzsaSzemeredi.Upper.V008

-- Integer square root by bisection: with `lo² ≤ d < hi²`, returns the largest `k` with `k² ≤ d`.
def isqrtAux (d : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      let mid := (lo + hi) / 2
      if mid = lo then lo
      else if mid * mid ≤ d then isqrtAux d fuel mid hi else isqrtAux d fuel lo mid

def isqrt (d : ℕ) : ℕ := isqrtAux d (d + 2) 0 (d + 1)

-- V007's bound on `2 s` at a vertex with `t` triangles, halved: `s ≤ min(T + t, t(n+c)/2 − t²)`.
def capAB (n T t : ℕ) : ℕ := SqueezeBench.RuzsaSzemeredi.Upper.V007.cap n T t / 2

-- The pair inequality averaged over the non-neighbours of a vertex with `t ≥ 1` triangles and
-- `m = n − 1 − 2t ≥ 1` non-neighbours gives `A s² − B s + C ≤ 0` for `s = Σ_{u ∈ N(v)} t_u`;
-- `capP` is the floor of the larger root (or `0` when there is none).
def capP (n T t : ℕ) : ℕ :=
  let m : ℤ := (n : ℤ) - 1 - 2 * t
  let A : ℤ := 4 * (m + t)
  let B : ℤ := 2 * t * (8 * t + 13 * m + m * m)
  let C : ℤ := 16 * t ^ 3 + 30 * t ^ 2 * m + 4 * t ^ 2 * m ^ 2 + t * m ^ 2 - t * m ^ 3
    + 6 * T * t * m
  let D : ℤ := B * B - 4 * A * C
  if D < 0 then 0 else ((B + isqrt D.toNat) / (2 * A)).toNat

def cap' (n T t : ℕ) : ℕ :=
  if 1 ≤ t ∧ 2 * t + 1 < n then min (capAB n T t) (capP n T t) else capAB n T t

-- `ψ t = 4t² − 2·cap' t`, a lower bound on `4 t_v² − 2 s_v` at every vertex with `t_v = t`.
def psi (n T t : ℕ) : ℤ := 4 * (t : ℤ) ^ 2 - 2 * (cap' n T t : ℤ)

-- Does the line through `(q, a)` and `(q+1, b)` exceed `ψ` at some `t ≤ bound`?
def lineAbove (n T q : ℕ) (a b : ℤ) : ℕ → Bool
  | 0 => decide (psi n T 0 < a + (b - a) * (0 - (q : ℤ)))
  | t + 1 => decide (psi n T (t + 1) < a + (b - a) * ((t + 1 : ℕ) - (q : ℤ))) || lineAbove n T q a b t

-- The test: `T` cannot be excluded if the balanced value is `≤ 0`, or if the chord through the
-- balanced points fails to lie below `ψ` somewhere on `[0, (n−1)/2]`.
def ok (n T : ℕ) : Bool :=
  let q := 3 * T / n
  let r := 3 * T % n
  let a := psi n T q
  let b := psi n T (q + 1)
  decide (((n : ℤ) - r) * a + r * b ≤ 0) || lineAbove n T q a b ((n - 1) / 2)

def search (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => cond (ok n (T + 1)) (T + 1) (search n T)

def record : SqueezeBench.BoundFn :=
  fun n => search n (SqueezeBench.RuzsaSzemeredi.Upper.V007.record n)

end SqueezeBench.RuzsaSzemeredi.Upper.V008
