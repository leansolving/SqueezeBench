import SqueezeBench.Problems.Ramsey.Records.Lower.V007.Def

/-! Record V008 for Ramsey, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/Ramsey/Lower/V008.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md).

The bound is `max over a, b, c, d of 5^a·17^b·37^c·101^d·⌊(n−1)/(2^a·3^b·4^c·5^d)⌋² + 1`:
`a` levels of the 5-cycle over `b` levels of the Paley graph on 17 vertices over `c` levels
of the Paley graph on 37 vertices over `d` levels of the Paley graph on 101 vertices (clique
and independence number 5, the graph behind `R(6,6) > 101`) over a block graph. Four nested
folds, each stopping as soon as its clique factor exceeds `n − 1`. -/

namespace SqueezeBench.Ramsey.Lower.V008

-- Levels of the Paley graph on 101 vertices (clique factor 5), innermost; `dd` is the clique
-- factor and `p` the vertex factor accumulated so far.
def goD (m : ℕ) (fuel dd p : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < dd then 0 else max (p * (m / dd) ^ 2) (goD m fuel (5 * dd) (101 * p))

-- Levels of the Paley graph on 37 vertices (factor 4), each opening a fold over the 101-levels.
def goC (m : ℕ) (fuel dd p : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < dd then 0 else max (goD m (fuel + 1) dd p) (goC m fuel (4 * dd) (37 * p))

-- Levels of the Paley graph on 17 vertices (factor 3).
def goB (m : ℕ) (fuel dd p : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < dd then 0 else max (goC m (fuel + 1) dd p) (goB m fuel (3 * dd) (17 * p))

-- Levels of the 5-cycle (factor 2), outermost.
def goA (m : ℕ) (fuel dd p : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if m < dd then 0 else max (goB m (fuel + 1) dd p) (goA m fuel (2 * dd) (5 * p))

def v : SqueezeBench.BoundFn :=
  SqueezeBench.pin SqueezeBench.Ramsey.nMin (fun n => goA (n - 1) n 1 1 + 1)

def record : SqueezeBench.BoundFn := SqueezeBench.maxWith SqueezeBench.Ramsey.Lower.V007.record v

end SqueezeBench.Ramsey.Lower.V008
