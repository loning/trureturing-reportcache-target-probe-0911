/- GID: D5/S1/Digit/Admissibility/WindowCapacityExtrema
   generality: I
   mirror-B: D5/B/S1/Digit/Admissibility/WindowCapacityExtrema
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximizing products of Fibonacci window sizes forces the exact extremal width shapes. -/

import D5.S0.Conventions.WDigits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S1.Digit.Admissibility.WindowCapacityExtrema

open D5.S0.Conventions
open scoped BigOperators

/-- Width vectors with a prescribed total width. -/
def feasibleWidths (k B : ℕ) : Set (Fin k → ℕ) :=
  {L | ∑ i, L i = B}

/-- The number of states in the product of the specified Fibonacci windows. -/
def windowProduct {k : ℕ} (L : Fin k → ℕ) : ℕ :=
  ∏ i, wValue (L i)

/-- Below the register count the widths are zero or one; above it all but one are one. -/
def ExtremalShape {k : ℕ} (B : ℕ) (L : Fin k → ℕ) : Prop :=
  (B ≤ k → ∀ i, L i ≤ 1) ∧
  (k ≤ B → ∃ i, L i = B - k + 1 ∧ ∀ j, j ≠ i → L j = 1)

end D5.S1.Digit.Admissibility.WindowCapacityExtrema
