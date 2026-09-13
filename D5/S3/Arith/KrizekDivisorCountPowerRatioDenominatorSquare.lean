/- GID: D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare
   generality: G
   mirror-B: D5/B/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.Data.Rat.Lemmas, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: OEIS A302975: every reduced denominator of tau(n)^n / n^tau(n) is a square. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.KrizekDivisorCountPowerRatioDenominatorSquare

/-- The reduced denominator of `tau(n)^n / n^tau(n)`, as in OEIS A302975.
At `n = 0` this definition has the totalized value `1`; the source claim starts at `n = 1`. -/
def D (n : ℕ) : ℕ :=
  (((Nat.divisors n).card : ℚ) ^ n /
    (n : ℚ) ^ (Nat.divisors n).card).den

#eval (List.range 20).map fun k => D (k + 1)

end D5.S3.Arith.KrizekDivisorCountPowerRatioDenominatorSquare
