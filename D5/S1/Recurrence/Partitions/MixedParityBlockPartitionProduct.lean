/- GID: D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   generality: G
   mirror-B: D5/B/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Order.Partition.Finpartition, Mathlib.Data.Fintype.Powerset, Mathlib.Data.Fintype.Sigma, Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: Marked set partitions and the odd-even mixed-block product conjecture. -/

import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators

namespace D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct

open Finset

/-- Set partitions of an `r`-element labelled set. -/
abbrev SetPartition (r : ℕ) := Finpartition (univ : Finset (Fin r))

/-- Stirling numbers of the second kind, defined by their partition cardinality. -/
def stirling2 (r i : ℕ) : ℕ :=
  Fintype.card {P : SetPartition r // P.parts.card = i}

/-- A set partition together with exactly `k` distinguished blocks. -/
abbrev MarkedPartition (r k : ℕ) :=
  Σ P : SetPartition r, {M : Finset P.parts // M.card = k}

/-- The number of partitions of an `r`-set with exactly `k` distinguished blocks. -/
def markedPartitions (r k : ℕ) : ℕ := Fintype.card (MarkedPartition r k)

/-- OEIS A049020 in its Stirling-number form. -/
def A049020 (r k : ℕ) : ℕ :=
  ∑ i ∈ range (r + 1), stirling2 r i * i.choose k

/-- Marking `k` blocks after partitioning gives the Stirling-binomial formula for A049020. -/
theorem markedPartitions_eq_A049020 (r k : ℕ) :
    markedPartitions r k = A049020 r k := by
  classical
  rw [markedPartitions, A049020]
  change Fintype.card (Σ P : SetPartition r, {M : Finset P.parts // M.card = k}) = _
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_finset_len]
  simp_rw [Fintype.card_coe]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (univ : Finset (SetPartition r)))
    (t := range (r + 1))
    (g := fun P : SetPartition r => P.parts.card)
    (f := fun P : SetPartition r => P.parts.card.choose k)]
  · apply sum_congr rfl
    intro i hi
    calc
      ∑ P : SetPartition r with P.parts.card = i, P.parts.card.choose k =
          ((univ.filter fun P : SetPartition r => P.parts.card = i).card) * i.choose k := by
            apply Finset.sum_const_nat
            intro P hP
            rw [(mem_filter.mp hP).2]
      _ = stirling2 r i * i.choose k := by
        congr 1
        simp [stirling2, Fintype.card_subtype]
  · intro P _
    rw [mem_range]
    exact Nat.lt_succ_of_le (by simpa using P.card_parts_le_card)

#print axioms markedPartitions_eq_A049020

end D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct
