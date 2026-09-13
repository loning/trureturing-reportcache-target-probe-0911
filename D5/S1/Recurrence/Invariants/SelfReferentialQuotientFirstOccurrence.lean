/- GID: D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Basic]
   utility: none
   digest: The first occurrence thresholds of Alkan's self-referential quotient recurrence. -/

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# First occurrences in a self-referential quotient recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
the source sequence starts at index one.
-/

namespace D5.S1.Recurrence.Invariants.SelfReferentialQuotientFirstOccurrence

/-- Alkan's sequence A335925, totalized at index zero by the sentinel value one. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => a ((n + 1) / a (n + 1)) + 1
termination_by n => n
decreasing_by
  · omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- A000522 in its recurrence form. -/
def T : ℕ → ℕ
  | 0 => 1
  | r + 1 => (r + 1) * T r + 1

#eval (List.range 40).map fun i => a (i + 1)

end D5.S1.Recurrence.Invariants.SelfReferentialQuotientFirstOccurrence
