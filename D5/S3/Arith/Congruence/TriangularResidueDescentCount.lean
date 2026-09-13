/- GID: D5/S3/Arith/Congruence/TriangularResidueDescentCount
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/TriangularResidueDescentCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Count the descents in the triangular-number permutation modulo each positive power of two. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.TriangularResidueDescentCount

/-- The `k`-th triangular number reduced modulo `2 ^ n`, as in OEIS A329278. -/
def T (n k : ℕ) : ℕ :=
  (k * (k + 1) / 2) % 2 ^ n

/-- The number of adjacent strict descents in row `n` of OEIS A329278. -/
def descents (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n - 1)).filter (fun k => T n (k + 1) < T n k)).card

end D5.S3.Arith.Congruence.TriangularResidueDescentCount
