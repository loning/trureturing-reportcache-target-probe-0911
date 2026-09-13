/- GID: D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Archimedean.Real.Basic, mathlib/module/Mathlib.Algebra.Order.Floor.Ring, mathlib/module/Mathlib.Data.Finset.Interval, mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.Ring, mathlib/module/Mathlib.Topology.Instances.Real.Lemmas, mathlib/module/Mathlib.Topology.Order.IntermediateValue]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.claim; result=D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.result; claim=D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.claim
   digest: At n = 1167, the literal nested recurrence is 664 while the conjectured cubic-root floor is 665. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.CloitreNestedRecurrenceFloorRefutation

/-!
OEIS A076502, entered by Benoit Cloitre on 2002-11-08, defines
`a(1)=1, a(n)=n-a(n-a(n-a(n-1))).`  The value at zero below is only a
sentinel outside the offset-one sequence.

The recursive implementation clamps the two computed inner indices below the
current input.  A strong-induction invariant proves that both clamps are
identities, so the public sequence satisfies the literal recurrence without a
fuel convention.
-/

/-- The offset-one A076502 sequence, extended by the disclosed sentinel `a 0 = 0`. -/
def a : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let i2 := min (n + 2 - a (n + 1)) (n + 1)
      let i3 := min (n + 2 - a i2) (n + 1)
      n + 2 - a i3
termination_by n => n
decreasing_by all_goals omega

private theorem a_bounds (N : ℕ) : a N <= N /\ (0 < N -> 0 < a N) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      rcases N with _ | _ | n
      · simp [a]
      · simp [a]
      · rw [a]
        let i2 := min (n + 2 - a (n + 1)) (n + 1)
        let i3 := min (n + 2 - a i2) (n + 1)
        have h1 := ih (n + 1) (by omega)
        have hi2le : i2 <= n + 1 := min_le_right _ _
        have hi2pos : 0 < i2 := by
          have hraw : 0 < n + 2 - a (n + 1) := by omega
          simp only [i2, lt_min_iff]
          omega
        have h2 := ih i2 (by omega)
        have hi3le : i3 <= n + 1 := min_le_right _ _
        have hi3pos : 0 < i3 := by
          have hraw : 0 < n + 2 - a i2 := by omega
          simp only [i3, lt_min_iff]
          omega
        have h3 := ih i3 (by omega)
        change n + 2 - a i3 <= n + 2 /\ (0 < n + 2 -> 0 < n + 2 - a i3)
        omega

private theorem a_succ (n : ℕ) :
    a (n + 2) = n + 2 - a (n + 2 - a (n + 2 - a (n + 1))) := by
  rw [a]
  have h1 := a_bounds (n + 1)
  have hi2le : n + 2 - a (n + 1) <= n + 1 := by omega
  rw [min_eq_left hi2le]
  have hi2pos : 0 < n + 2 - a (n + 1) := by omega
  have h2 := a_bounds (n + 2 - a (n + 1))
  have hi3le : n + 2 - a (n + 2 - a (n + 1)) <= n + 1 := by omega
  rw [min_eq_left hi3le]

private def P (x : ℝ) : ℝ := x ^ 3 - x ^ 2 + 2 * x - 1

private theorem P_strictMono : StrictMono P := by
  intro x y hxy
  have hfactor : 0 < y ^ 2 + y * x + x ^ 2 - y - x + 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y - 1)]
  have hdiff : P y - P x =
      (y - x) * (y ^ 2 + y * x + x ^ 2 - y - x + 2) := by
    simp only [P]
    ring
  have hprod : 0 < (y - x) * (y ^ 2 + y * x + x ^ 2 - y - x + 2) :=
    mul_pos (sub_pos.mpr hxy) hfactor
  linarith

private theorem existsUniquePositiveRoot : ∃! x : ℝ, 0 < x /\ P x = 0 := by
  have hcontinuous : Continuous P := by
    unfold P
    exact ((((continuous_id.pow 3).sub (continuous_id.pow 2)).add
      (continuous_const.mul continuous_id)).sub continuous_const)
  have hzero : (0 : ℝ) ∈ Set.Icc (P 0) (P 1) := by
    norm_num [P]
  obtain ⟨x, hx, hPx⟩ :=
    intermediate_value_Icc (show (0 : ℝ) <= 1 by norm_num)
      hcontinuous.continuousOn hzero
  have hxpos : 0 < x := by
    rcases hx with ⟨hxnonneg, _⟩
    by_contra hnot
    have : x = 0 := by linarith
    subst x
    norm_num [P] at hPx
  refine ⟨x, ⟨hxpos, hPx⟩, ?_⟩
  intro y hy
  apply P_strictMono.injective
  exact hy.2.trans hPx.symm

/-- The unique positive real root of `x^3 - x^2 + 2*x - 1`. -/
noncomputable def c : ℝ := Classical.choose existsUniquePositiveRoot

/-- Cloitre's literal 2002 comment: bounded real error and floor offset in `{0,1,2}`. -/
def claim : Prop :=
  (∃ M : ℝ, ∀ n : ℕ, 1 <= n -> |(a n : ℝ) - c * n| <= M) /\
    ∀ n : ℕ, 1 <= n -> ∃ j ∈ ({0, 1, 2} : Finset ℤ),
      (a n : ℤ) = ⌊c * n⌋ + j

end D5.S1.Recurrence.Invariants.CloitreNestedRecurrenceFloorRefutation
