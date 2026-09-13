/- GID: D5/S0/Rewriting/BoundedSuccessorObservationCount
   generality: G
   mirror-B: D5/B/S0/Rewriting/BoundedSuccessorObservationCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict bounded successor trajectories reach an absorbing failure exactly at the arithmetic boundary. -/

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Omega

set_option autoImplicit false

namespace D5.S0.Rewriting.BoundedSuccessorObservationCount

/-! The totalized strict successor on natural-number states bounded by `B`. -/
def strictSuccessor (B : ℕ) : Option ℕ → Option ℕ
  | none => none
  | some n => if n < B then some (n + 1) else none

/-! The state reached after `t` applications of the bounded successor. -/
def trajectory (B n t : ℕ) : Option ℕ :=
  (strictSuccessor B)^[t] (some n)

/-- The trajectory has the stated arithmetic form, and the boundary transition is the
absorbing failure occurring at time `B - n + 1`. -/
theorem bounded_successor_trajectory (B n : ℕ) (hn : n ≤ B) :
    (∀ t : ℕ,
      trajectory B n t = if n + t ≤ B then some (n + t) else none) ∧
    trajectory B n (B - n) = some B ∧
    trajectory B n (B - n + 1) = none := by
  have htraj : ∀ t : ℕ,
      trajectory B n t = if n + t ≤ B then some (n + t) else none := by
    intro t
    induction t with
    | zero => simp [trajectory, hn]
    | succ t ih =>
        rw [trajectory, Function.iterate_succ_apply', ih]
        by_cases ht : n + t ≤ B
        · rw [if_pos ht]
          by_cases hlt : n + t < B
          · simp [strictSuccessor, hlt,
              show n + (t + 1) ≤ B by omega, Nat.add_assoc]
          · simp [strictSuccessor, hlt,
              show ¬ n + (t + 1) ≤ B by omega]
        · simp [ht, strictSuccessor,
            show ¬ n + (t + 1) ≤ B by omega]
  refine ⟨htraj, ?_, ?_⟩
  · rw [htraj]
    rw [if_pos (by omega)]
    congr 1
    omega
  · rw [htraj]
    rw [if_neg (by omega)]

end D5.S0.Rewriting.BoundedSuccessorObservationCount
