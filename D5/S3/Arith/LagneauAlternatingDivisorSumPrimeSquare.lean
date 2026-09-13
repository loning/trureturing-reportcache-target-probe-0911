/- GID: D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
   generality: G
   mirror-B: D5/B/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A prime alternating sum of decreasing divisors above three forces a square or twice a square. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.LagneauAlternatingDivisorSumPrimeSquare

open scoped ArithmeticFunction

/-- The alternating sum of all divisors of `n`, in nonincreasing order starting with `n`. -/
def T (n : ℕ) : ℤ :=
  ((n.divisors.sort (· ≥ ·)).map fun d ↦ (d : ℤ)).alternatingSum

private theorem alternatingSum_nonneg_of_pairwise_ge :
    ∀ l : List ℕ, l.Pairwise (· ≥ ·) →
      0 ≤ (l.map fun d ↦ (d : ℤ)).alternatingSum
  | [], _ => by simp
  | [a], _ => by simp [List.alternatingSum]
  | a :: b :: l, hsorted => by
      simp only [List.pairwise_cons] at hsorted
      have hab : b ≤ a := hsorted.1 b (by simp)
      have htail : l.Pairwise (· ≥ ·) := hsorted.2.2
      have ih := alternatingSum_nonneg_of_pairwise_ge l htail
      change 0 ≤ (a : ℤ) + -(b : ℤ) + (l.map fun d ↦ (d : ℤ)).alternatingSum
      omega

#eval (List.range 20).map fun i ↦ T (i + 1)

end D5.S3.Arith.LagneauAlternatingDivisorSumPrimeSquare
