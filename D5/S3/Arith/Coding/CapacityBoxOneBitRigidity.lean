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

open scoped symmDiff

private def flipSupport {B : Nat} (x y : Fin B → Bool) : Finset (Fin B) :=
  Finset.univ.filter fun j => x j ≠ y j

private theorem flipSupport_card_one {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : (flipSupport x y).card = 1 := by
  simpa [flipSupport, hammingDist]

private theorem flipSupport_eq_singleton {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : ∃ a : Fin B, flipSupport x y = {a} := by
  exact Finset.card_eq_one.mp (flipSupport_card_one h)

noncomputable def edgeColour {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : Fin B :=
  Classical.choose (flipSupport_eq_singleton h)

private theorem flipSupport_eq_edgeColour {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : flipSupport x y = {edgeColour h} :=
  Classical.choose_spec (flipSupport_eq_singleton h)

private theorem flipSupport_xor {B : Nat} (x y z : Fin B → Bool) :
    flipSupport x z = flipSupport x y ∆ flipSupport y z := by
  classical
  ext i
  simp only [flipSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  by_cases hxy : x i = y i <;> by_cases hyz : y i = z i
  · simp [hxy, hyz]
  · simp [hxy, hyz]
  · simp [hxy, hyz]
  · cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp_all

private theorem singleton_symmDiff_singleton_eq {B : Nat} {p q r s : Fin B}
    (h : ({p} : Finset (Fin B)) ∆ {q} = ({r} : Finset (Fin B)) ∆ {s})
    (hpq : p ≠ q) : p = r ∨ p = s := by
  have hp : p ∈ ({p} : Finset (Fin B)) ∆ {q} := by
    rw [Finset.mem_symmDiff]
    exact Or.inl ⟨by simp, by simpa using hpq⟩
  rw [h] at hp
  have hp' : p = r ∧ p ≠ s ∨ p = s ∧ p ≠ r := by
    simpa [Finset.mem_symmDiff] using hp
  exact hp'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- Opposite edges of a nondegenerate Boolean square have the same colour. -/
theorem square_opposite_edges_same_colour {B : Nat}
    (a b c d : Fin B → Bool)
    (hab : hammingDist a b = 1) (hbd : hammingDist b d = 1)
    (hac : hammingDist a c = 1) (hcd : hammingDist c d = 1)
    (had : a ≠ d) (hbc : b ≠ c) :
    edgeColour hab = edgeColour hcd := by
  classical
  let p := edgeColour hab
  let q := edgeColour hbd
  let r := edgeColour hac
  let s := edgeColour hcd
  have hs1 : flipSupport a b = {p} := flipSupport_eq_edgeColour hab
  have hs2 : flipSupport b d = {q} := flipSupport_eq_edgeColour hbd
  have hs3 : flipSupport a c = {r} := flipSupport_eq_edgeColour hac
  have hs4 : flipSupport c d = {s} := flipSupport_eq_edgeColour hcd
  have hxor : (({p} : Finset (Fin B)) ∆ {q}) = (({r} : Finset (Fin B)) ∆ {s}) := by
    calc
      ({p} : Finset (Fin B)) ∆ {q} = flipSupport a b ∆ flipSupport b d := by rw [hs1, hs2]
      _ = flipSupport a c ∆ flipSupport c d := by
        rw [← flipSupport_xor a b d, ← flipSupport_xor a c d]
      _ = ({r} : Finset (Fin B)) ∆ {s} := by rw [hs3, hs4]
  have hpq : p ≠ q := by
    intro heq
    have : a = d := by
      have hsd : flipSupport a d = ∅ := by
        rw [flipSupport_xor a b d, hs1, hs2, heq]
        simp
      funext t
      by_contra hne
      have ht : t ∈ flipSupport a d := by simp [flipSupport, hne]
      rw [hsd] at ht
      simpa using ht
    exact had this
  rcases singleton_symmDiff_singleton_eq hxor hpq with hpr | hps
  · have hsup : flipSupport a b = flipSupport a c := by rw [hs1, hs3, hpr]
    have hbcEq : b = c := by
      funext t
      have hm : t ∈ flipSupport a b ↔ t ∈ flipSupport a c := by rw [hsup]
      simp only [flipSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      cases hx : a t <;> cases hy : b t <;> cases hz : c t <;> simp_all
    exact False.elim (hbc hbcEq)
  · simpa [p, s] using hps

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
