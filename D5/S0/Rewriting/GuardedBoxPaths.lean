/- GID: D5/S0/Rewriting/GuardedBoxPaths
   generality: G
   mirror-B: D5/B/S0/Rewriting/GuardedBoxPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Guarded unit words obey coordinate distance bounds with equality precisely for endpoint-directed instructions. -/

import Mathlib.Data.List.Count
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace D5.S0.Rewriting.GuardedBoxPaths

variable {P : Type*} [DecidableEq P]

/-- A unit instruction selects a coordinate and increases it when its Boolean is true. -/
abbrev Instruction (P : Type*) := P × Bool

/-- A unit update fails at the upper capacity or at zero, respectively. -/
def step (A a : P → ℕ) (s : Instruction P) : Option (P → ℕ) :=
  if s.2 then
    if a s.1 < A s.1 then some (Function.update a s.1 (a s.1 + 1)) else none
  else
    if 0 < a s.1 then some (Function.update a s.1 (a s.1 - 1)) else none

/-- Evaluate a word from left to right, failing as soon as a unit guard fails. -/
def eval (A a : P → ℕ) : List (Instruction P) → Option (P → ℕ)
  | [] => some a
  | s :: w => (step A a s).bind (fun b => eval A b w)

/-- A path starts inside the capacity box and reaches its endpoint through guarded updates. -/
def LegalPath (A a b : P → ℕ) (w : List (Instruction P)) : Prop :=
  (∀ p, a p ≤ A p) ∧ eval A a w = some b

/-- The number of instructions acting on one coordinate, in either direction. -/
def coordinateCount (w : List (Instruction P)) (p : P) : ℕ :=
  w.count (p, true) + w.count (p, false)

/-- The sum of absolute integer coordinate differences between two natural configurations. -/
def distance [Fintype P] (a b : P → ℕ) : ℕ :=
  ∑ p, ((b p : ℤ) - (a p : ℤ)).natAbs

/-- Every instruction on this coordinate strictly approaches its final coordinate value. -/
def TowardEndpoint (a b : P → ℕ) (w : List (Instruction P)) (p : P) : Prop :=
  ((p, true) ∈ w → a p < b p) ∧ ((p, false) ∈ w → b p < a p)

/-- Successful guarded evaluation gives the signed difference of the two instruction counts. -/
theorem endpoint_counts (A a b : P → ℕ) (w : List (Instruction P))
    (h : eval A a w = some b) (p : P) :
    (b p : ℤ) - (a p : ℤ) =
      (w.count (p, true) : ℤ) - (w.count (p, false) : ℤ) := by
  induction w generalizing a with
  | nil =>
    simp only [eval, Option.some.injEq] at h
    subst b
    simp
  | cons s w ih =>
    obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.mp h
    rcases s with ⟨q, up⟩
    cases up with
    | false =>
      by_cases hg : 0 < a q
      · simp only [step, Bool.false_eq_true, ↓reduceIte, hg, Option.some.injEq] at hx
        subst x
        have tail := ih _ hw
        by_cases hp : p = q
        · subst p
          simp only [Function.update_self] at tail
          simp_all [List.count_cons]
          omega
        · simpa [Function.update_of_ne hp, List.count_cons, hp, Ne.symm hp] using tail
      · simp [step, hg] at hx
    | true =>
      by_cases hg : a q < A q
      · simp only [step, ↓reduceIte, hg, Option.some.injEq] at hx
        subst x
        have tail := ih _ hw
        by_cases hp : p = q
        · subst p
          simp only [Function.update_self] at tail
          simp_all [List.count_cons]
          omega
        · simpa [Function.update_of_ne hp, List.count_cons, hp, Ne.symm hp] using tail
      · simp [step, hg] at hx

end D5.S0.Rewriting.GuardedBoxPaths
