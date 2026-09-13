/- GID: D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: First occurrence thresholds in Alkan's self-referential doubling recurrence. -/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# First occurrences in a self-referential doubling recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
the source sequence starts at index one.
-/

namespace D5.S1.Recurrence.Invariants.SelfReferentialDoublingFirstOccurrence

/-- Alkan's sequence A335901, totalized at index zero by the sentinel value one. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * a ((n + 1) / a (n + 1))
termination_by n => n
decreasing_by
  · omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- A117261 in its recurrence form. -/
def T : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 ^ r * T r + 1

#eval (List.range 40).map (fun n => a (n + 1))

end D5.S1.Recurrence.Invariants.SelfReferentialDoublingFirstOccurrence
