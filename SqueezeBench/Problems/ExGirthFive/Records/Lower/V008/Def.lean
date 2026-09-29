import SqueezeBench.Problems.ExGirthFive.Records.Lower.V007.Def

/-! Record V008 for ExGirthFive, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V008.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V008

-- Number of slope classes of the sub-plane placed on `r < 2p²` leftover vertices: `⌈r/(2p)⌉`.
def slopes (p r : ℕ) : ℕ := (r + 2 * p - 1) / (2 * p)

-- The sub-plane on `r` vertices: `s = slopes p r` slope classes of the affine plane over `ZMod p`,
-- i.e. `s·p` lines, and `r − s·p` of its points; each point lies on one line of each class, so
-- it has `s · (r − s·p)` edges. (`s·p ≤ r` fails only when the product is `0` anyway.)
def part (p r : ℕ) : ℕ := slopes p r * (r - slopes p r * p)

-- For the prime `p`: `⌊n/(2p²)⌋` full affine planes (`p³` edges each) and a sub-plane on the
-- `n mod 2p²` leftover vertices.
def blk (p n : ℕ) : ℕ := p * p * p * (n / (2 * p * p)) + part p (n % (2 * p * p))

-- The primes `2, 3, 5, 7` (for small `n`), one prime near the geometric mean of each pair of
-- consecutive entries of the V007 table (halving its ratio `1.19` to about `1.09`), and the V007
-- table itself.
def primes : List ℕ :=
  [2, 3, 5, 7, 29, 37, 41, 53, 67, 79, 89, 107, 127, 157, 181, 223, 263, 317, 379, 449, 541,
   641, 761, 907, 1087, 1283, 1531, 1823, 2161, 2579, 3061, 3643, 4337, 5153, 6133, 7297,
   8681, 10321, 12277, 14593, 17359, 20639, 24551, 29209, 34739, 41299, 49123, 58417, 69481,
   82633, 98251, 116833, 138967, 165247, 196523, 233713, 277961, 330509, 393059, 467437,
   555871, 661049, 786127, 934883, 1111757, 1322117, 1572271, 1869757, 2223541, 2644247,
   3144551, 3739531, 4447099, 5288489, 6289121, 7479089, 8894173, 10577003, 12578303,
   14958169, 17788367, 21154039, 25156561, 29916361, 35576743, 42308113, 50313119, 59832727,
   71153527, 84616223, 100626233, 119665433, 142306993, 169232513, 201252517, 239330941,
   284614021, 338464991, 402505009, 478661879, 569228083, 676930073, 805010083, 957323711,
   1138456159, 1353860147, 1610020169, 1914647437] ++ SqueezeBench.ExGirthFive.Lower.V007.primes

-- The best prime of the table at each `n`: full planes plus a sub-plane on the leftover.
def blocks : SqueezeBench.BoundFn := fun n => (primes.map fun p => blk p n).foldr max 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V007.record blocks

end SqueezeBench.ExGirthFive.Lower.V008
