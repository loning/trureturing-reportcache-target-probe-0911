/- GID: D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.NumberTheory.PrimeCounting, mathlib/module/Mathlib.Data.Nat.Factorization.Basic]
   utility: none
   digest: Wiseman's A258409 divisor-minus-one gcd equals the consecutive divisor-gap gcd and its Heinz prime-index gcd.
 -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

noncomputable def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

noncomputable def consecutiveDivisorDifferences (n : ℕ) : List ℕ :=
  (divisorList n).zipWith (fun x y => y - x) (divisorList n).tail

def a (n : ℕ) : ℕ := n.divisors.gcd (fun d => d - 1)

noncomputable def consecutiveDifferenceGcd (n : ℕ) : ℕ :=
  (consecutiveDivisorDifferences n).toFinset.gcd id

noncomputable def heinzDifferences (n : ℕ) : ℕ :=
  ((consecutiveDivisorDifferences n).map (fun d => Nat.nth Nat.Prime (d - 1))).prod

noncomputable def primeIndexGcd (m : ℕ) : ℕ := m.primeFactors.gcd Nat.primeCounting

theorem wiseman_a258409 : ∀ n, 2 ≤ n →
    a n = primeIndexGcd (heinzDifferences n) ∧
      a n = consecutiveDifferenceGcd n := by
  intro n hn
  sorry

end D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz
