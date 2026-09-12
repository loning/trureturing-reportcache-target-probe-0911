/- GID: D5/S1/Words/Mechanical/JointRotationFactorComplexity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/JointRotationFactorComplexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous integer-scale rotation words have complexity at most the total circular boundary count. -/

import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import D5.S1.Words.Mechanical.FloorFractShift

set_option autoImplicit false

noncomputable section

namespace D5.S1.Words.Mechanical.JointRotationFactorComplexity

open scoped BigOperators

open Classical in
/-- The length-`h` vector word at phase `x`, with threshold `{a * α}` at scale `a`. -/
def jointRotationFactor (α : ℝ) (b : ℕ → ℤ) (A : Finset ℕ) (h : ℕ)
    (x : ℝ) : Fin h → A → ℤ := fun j a =>
  b a - if 1 - Int.fract ((a : ℝ) * α) ≤
    Int.fract ((a : ℝ) * (x + (j : ℝ) * α) + α) then 1 else 0

/-- The vector words realized by phases on the unit circle, represented by `[0,1)`. -/
def jointRotationFactorSet (α : ℝ) (b : ℕ → ℤ) (A : Finset ℕ) (h : ℕ) :
    Set (Fin h → A → ℤ) :=
  jointRotationFactor α b A h '' Set.Ico 0 1

/-- For nonempty positive scales, the number of simultaneous rotation words of length `h`
is at most `(h + 1) * ∑ a ∈ A, a`. -/
theorem joint_rotation_factor_complexity (α : ℝ) (b : ℕ → ℤ)
    (A : Finset ℕ) (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a) (h : ℕ) :
    (jointRotationFactorSet α b A h).Finite ∧
      (jointRotationFactorSet α b A h).ncard ≤ (h + 1) * ∑ a ∈ A, a := by
  sorry

end D5.S1.Words.Mechanical.JointRotationFactorComplexity
