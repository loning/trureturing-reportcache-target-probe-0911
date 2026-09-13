/- GID: D5/S1/Digit/Infinite/SuccessorContinuity
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/SuccessorContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first adjacent zero erasure successor is continuous on infinite legal Boolean digits. -/

import Mathlib.Data.Nat.Find
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SuccessorContinuity

open scoped Topology

/-- Infinite Boolean digit sequences with no adjacent ones, with the product subspace topology. -/
def LegalDigits := {x : ℕ → Bool // ∀ j, ¬ (x j = true ∧ x (j + 1) = true)}

/-- Erase all digits below the first adjacent zero pair and put a one at its first position;
if there is no adjacent zero pair, return the zero sequence. -/
noncomputable def next (x : ℕ → Bool) : ℕ → Bool := by
  classical
  exact if h : ∃ j, x j = false ∧ x (j + 1) = false then
    let j := Nat.find h
    fun i => if i < j then false else if i = j then true else x i
  else fun _ => false

end D5.S1.Digit.Infinite.SuccessorContinuity
