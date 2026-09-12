/- GID: D5/S1/Digit/Carry/SuccessorShortest
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/SuccessorShortest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Token mass bounds the length of every directed Fibonacci carry path. -/

import D5.S1.Digit.Carry.Successor

set_option autoImplicit false

namespace D5.S1.Digit.Carry.SuccessorShortest

open D5.S1.Digit D5.S1.Digit.Carry.Successor

/-- Every directed carry path has at least the decrease in its total digit multiplicity steps. -/
theorem carry_steps_mass_lower_bound {k : Nat} {r s : RawDigits}
    (path : CarrySteps k r s) : tokenCount r ≤ tokenCount s + k := by
  classical
  induction path with
  | zero => omega
  | @succ k r middle s path step ih =>
    have decrease : tokenCount middle ≤ tokenCount s + 1 := by
      cases step <;> simp [tokenCount, Finsupp.sum_add_index]
    omega

end D5.S1.Digit.Carry.SuccessorShortest
