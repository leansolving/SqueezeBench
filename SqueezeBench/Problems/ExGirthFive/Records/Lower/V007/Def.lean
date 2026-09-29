import SqueezeBench.Problems.ExGirthFive.Records.Lower.V006.Def

/-! Record V007 for ExGirthFive, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/ExGirthFive/Lower/V007.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.ExGirthFive.Lower.V007

-- A dense table of primes: one just below each multiple of `2^(1/4)` from `11` to `2^31`, so that
-- consecutive entries differ by a factor of about `1.19` instead of the factor `2` of V006.
def primes : List ℕ :=
  [11, 13, 17, 19, 23, 31, 43, 47, 61, 73, 83, 103, 113, 139, 173, 199, 241, 293, 349, 409,
   491, 587, 701, 829, 991, 1181, 1399, 1669, 1987, 2357, 2803, 3347, 3967, 4733, 5623, 6691,
   7963, 9467, 11261, 13381, 15923, 18919, 22511, 26783, 31859, 37879, 45053, 53569, 63709,
   75773, 90107, 107137, 127423, 151549, 180221, 214309, 254873, 303097, 360439, 428639,
   509741, 606181, 720887, 857287, 1019479, 1212397, 1441771, 1714577, 2038979, 2424791,
   2883577, 3429157, 4078003, 4849589, 5767129, 6858353, 8156003, 9699161, 11534329, 13716713,
   16312003, 19398359, 23068667, 27433423, 32624023, 38796713, 46137319, 54866849, 65248049,
   77593447, 92274671, 109733711, 130496059, 155186893, 184549373, 219467431, 260992213,
   310373801, 369098707, 438934843, 521984459, 620747623, 738197503, 877869719, 1043968909,
   1241495239, 1476394991, 1755739439, 2087937811]

-- For each prime `p`, `⌊n/(2p²)⌋` disjoint copies of the point–line incidence graph of the affine
-- plane over `ZMod p`: `p²` points, `p²` lines, `p³` edges per block of `2p²` vertices, girth 6.
-- The envelope of these lines stays within a factor `1.19` of `(1/(2√2))·n^{3/2}` for every
-- `n ≤ 2·2087937811²`, ten million times the range of V006.
def blocks : SqueezeBench.BoundFn := fun n =>
  (primes.map fun p => p * p * p * (n / (2 * p * p))).foldr max 0

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.ExGirthFive.Lower.V006.record blocks

end SqueezeBench.ExGirthFive.Lower.V007
