/- GID: D5/S3/Arith/Coding/CapacityBoxOneBitRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/CapacityBoxOneBitRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A one-bit hypercube square has equal opposite edge colours. -/

import Mathlib.InformationTheory.Hamming
import D5.S1.Ledger.BoundedTimeSlice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.CapacityBoxOneBitRigidity

open scoped symmDiff

private def flipSupport {B : Nat} (x y : Fin B → Bool) : Finset (Fin B) :=
  Finset.univ.filter fun j => x j ≠ y j

/-- The colour of a unit Boolean edge is its unique changed bit. -/
noncomputable def edgeColour {B : Nat} {x y : Fin B → Bool}
    (h : hammingDist x y = 1) : Fin B :=
  Classical.choose (Finset.card_eq_one.mp (show (flipSupport x y).card = 1 from h))

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
  have hs1 : flipSupport a b = {p} := Classical.choose_spec (Finset.card_eq_one.mp hab)
  have hs2 : flipSupport b d = {q} := Classical.choose_spec (Finset.card_eq_one.mp hbd)
  have hs3 : flipSupport a c = {r} := Classical.choose_spec (Finset.card_eq_one.mp hac)
  have hs4 : flipSupport c d = {s} := Classical.choose_spec (Finset.card_eq_one.mp hcd)
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
  have hp : p ∈ ({p} : Finset (Fin B)) ∆ {q} := by simp [hpq]
  rw [hxor] at hp
  have hcases : p = r ∨ p = s := by
    rcases Finset.mem_symmDiff.mp hp with h | h
    · exact Or.inl (Finset.mem_singleton.mp h.1)
    · exact Or.inr (Finset.mem_singleton.mp h.1)
  rcases hcases with hpr | hps
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


open D5.S1.Ledger.BoundedTimeSlice (TailBox)

variable {P : Type*} [Fintype P] {A : P → ℕ}

/-- A directed unit edge increases one coordinate by one and fixes all others. -/
def UnitEdge (p : P) (a b : TailBox A) : Prop :=
  (b p).val = (a p).val + 1 ∧ ∀ q, q ≠ p → b q = a q

/-- An injective Boolean code sending each unit edge to Hamming distance one. -/
structure OneBitEmbedding (A : P → ℕ) (n : ℕ) where
  toFun : TailBox A → (Fin n → Bool)
  injective : Function.Injective toFun
  map_unitEdge : ∀ (p : P) (a b : TailBox A), UnitEdge p a b →
    hammingDist (toFun a) (toFun b) = 1

/-- Increase a coordinate whose current value is strictly below its capacity. -/
noncomputable def raise (a : TailBox A) (p : P) (h : (a p).val < A p) : TailBox A :=
  Function.update a p ⟨(a p).val + 1, Nat.add_lt_add_right h 1⟩

/-- The colour of the edge increasing the indicated coordinate. -/
noncomputable def unitEdgeColour {n : ℕ} (φ : OneBitEmbedding A n)
    (a : TailBox A) (p : P) (h : (a p).val < A p) : Fin n := by
  classical
  exact edgeColour (φ.map_unitEdge p a (raise a p h) (by
    constructor
    · simp [raise]
    · intro q hq
      simp [raise, hq]))


/-- Moving one step along another axis preserves the colour of a layer edge. -/
theorem layer_colour_invariant {n : ℕ} (φ : OneBitEmbedding A n)
    (a : TailBox A) (p q : P) (hpq : p ≠ q)
    (hp : (a p).val < A p) (hq : (a q).val < A q) :
    unitEdgeColour φ a p hp =
      unitEdgeColour φ (raise a q hq) p (by simpa [raise, hpq] using hp) := by
  classical
  let b := raise a p hp
  let c := raise a q hq
  have hcp : (c p).val < A p := by simpa [c, raise, hpq] using hp
  let d := raise c p hcp
  have hedge (x : TailBox A) (r : P) (hr : (x r).val < A r) :
      UnitEdge r x (raise x r hr) := by
    constructor
    · simp [raise]
    · intro t ht
      simp [raise, ht]
  have hbd : UnitEdge q b d := by
    constructor
    · simp [b, c, d, raise, hpq, Ne.symm hpq]
    · intro t ht
      by_cases htp : t = p
      · subst t
        simp [b, c, d, raise, hpq]
      · simp [b, c, d, raise, ht, htp]
  apply square_opposite_edges_same_colour (φ.toFun a) (φ.toFun b)
    (φ.toFun c) (φ.toFun d) (φ.map_unitEdge _ _ _ (hedge a p hp))
    (φ.map_unitEdge _ _ _ hbd) (φ.map_unitEdge _ _ _ (hedge a q hq))
    (φ.map_unitEdge _ _ _ (hedge c p hcp))
  · intro h
    have he := congrArg (fun x : TailBox A => (x p).val) (φ.injective h)
    simp [d, c, raise, hpq] at he
  · intro h
    have he := congrArg (fun x : TailBox A => (x p).val) (φ.injective h)
    simp [b, c, raise, hpq] at he


end D5.S3.Arith.Coding.CapacityBoxOneBitRigidity
