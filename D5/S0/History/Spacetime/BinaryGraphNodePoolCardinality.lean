/- GID: D5/S0/History/Spacetime/BinaryGraphNodePoolCardinality
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/BinaryGraphNodePoolCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact cardinality of the ordinal and Kuratowski nodes of a finite binary graph. -/

import D5.S0.History.Spacetime.HFEncoding
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace D5.S0.History.Spacetime.BinaryGraphNodePoolCardinality

noncomputable section

open HFEncoding (toZF natCode)

local notation "o" => fun n : ℕ => toZF (natCode n)

/-- The singleton of a finite von Neumann index. -/
def singletonNode (j : ℕ) : ZFSet.{0} := {o j}

/-- The unordered pair of an index and its binary value. -/
def doubleNode (b : ℕ → Bool) (j : ℕ) : ZFSet.{0} :=
  {o j, o (if b j then 1 else 0)}

/-- The Kuratowski pair of an index and its binary value. -/
def edge (b : ℕ → Bool) (j : ℕ) : ZFSet.{0} :=
  ZFSet.pair (o j) (o (if b j then 1 else 0))

/-- All ordinal indices, singletons, unordered bit pairs, and edges in a finite window. -/
def nodePool (ell : ℕ) (b : ℕ → Bool) : Finset ZFSet.{0} := by
  classical
  exact (Finset.range ell).image o ∪
    (Finset.range ell).image singletonNode ∪
    (Finset.range ell).image (doubleNode b) ∪
    (Finset.range ell).image (edge b)

end
end D5.S0.History.Spacetime.BinaryGraphNodePoolCardinality
