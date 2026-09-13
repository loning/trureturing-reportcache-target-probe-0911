/- GID: D5/S3/Arith/Coding/CapacityBoxOneBitRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/CapacityBoxOneBitRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A one-bit hypercube square has equal opposite edge colours. -/

import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.CapacityBoxOneBitRigidity

private def flipSupport {B : Nat} (x y : Fin B → Bool) : Finset (Fin B) :=
  Finset.univ.filter fun j => x j ≠ y j

private theorem flipSupport_card_one {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : (flipSupport x y).card = 1 := by
  simpa [flipSupport, hammingDist]

private theorem flipSupport_eq_singleton {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : ∃ a : Fin B, flipSupport x y = {a} := by
  exact Finset.card_eq_one.mp (flipSupport_card_one h)

/-- Two consecutive unit edges with the same flipped coordinate cannot form a diagonal. -/
theorem same_colour_adjacent_edges_force_diagonal {B : Nat}
    (x y z : Fin B → Bool) (a : Fin B)
    (hxy : flipSupport x y = {a})
    (hyz : flipSupport y z = {a}) :
    x = z := by
  have hxy' : ∀ t, x t ≠ y t ↔ t = a := by
    intro t
    rw [show x t ≠ y t ↔ t ∈ flipSupport x y by simp [flipSupport], hxy]
    simp
  have hyz' : ∀ t, y t ≠ z t ↔ t = a := by
    intro t
    rw [show y t ≠ z t ↔ t ∈ flipSupport y z by simp [flipSupport], hyz]
    simp
  funext t
  by_cases hta : t = a
  · subst t
    have hxyA : x a ≠ y a := (hxy' a).mpr rfl
    have hyzA : y a ≠ z a := (hyz' a).mpr rfl
    cases hx : x a <;> cases hy : y a <;> cases hz : z a <;> simp_all
  · have hxyEq : x t = y t := by
      by_contra h
      exact hta ((hxy' t).mp h)
    have hyzEq : y t = z t := by
      by_contra h
      exact hta ((hyz' t).mp h)
    exact hxyEq.trans hyzEq


end D5.S3.Arith.Coding.CapacityBoxOneBitRigidity
