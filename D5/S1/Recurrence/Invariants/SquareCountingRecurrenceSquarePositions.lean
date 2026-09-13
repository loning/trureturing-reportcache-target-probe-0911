/- GID: D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Interval.Finset.SuccPred, mathlib/module/Mathlib.Data.Nat.Sqrt, mathlib/module/Mathlib.Order.Interval.Finset.Nat, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Square positions and values in Zumkeller's square-counting recurrence. -/

import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Square positions in a square-counting recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
OEIS A097602 starts at index one.
-/

namespace D5.S1.Recurrence.Invariants.SquareCountingRecurrenceSquarePositions

private instance decidableIsSquareNat (n : ℕ) : Decidable (IsSquare n) :=
  decidable_of_iff (Nat.sqrt n * Nat.sqrt n = n) (by
    simpa only [IsSquare, eq_comm] using (Nat.exists_mul_self n).symm)

/-- OEIS A097602, totalized at index zero by the sentinel value zero. -/
def a (n : ℕ) : ℕ :=
  Nat.strongRec (motive := fun _ => ℕ) (fun n rec =>
    match n with
    | 0 => 0
    | 1 => 1
    | j + 2 =>
        rec (j + 1) (by omega) +
          ((Finset.Icc 1 (j + 1)).filter fun k =>
            IsSquare (if hk : k < j + 2 then rec k hk else 0)).card) n

end D5.S1.Recurrence.Invariants.SquareCountingRecurrenceSquarePositions
