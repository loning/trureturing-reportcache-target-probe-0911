/- GID: D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   generality: G
   mirror-B: D5/B/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Order.Partition.Finpartition, Mathlib.Data.Fintype.Powerset, Mathlib.Data.Fintype.Sigma, Mathlib.Data.Fintype.BigOperators, Mathlib.Data.Fintype.Perm]
   utility: none
   digest: Marked set partitions and the odd-even mixed-block product conjecture. -/

import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

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

/-- The canonical `n`-element parity-labelled set: the left summand labels odd entries. -/
abbrev ParityIndex (n : ℕ) := Fin ((n + 1) / 2) ⊕ Fin (n / 2)

/-- The parity-labelled carrier has exactly `n` elements. -/
theorem parityIndex_card (n : ℕ) : Fintype.card (ParityIndex n) = n := by
  simp only [ParityIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Set partitions of the parity-labelled `n`-element set. -/
abbrev ParityPartition (n : ℕ) :=
  Finpartition (univ : Finset (ParityIndex n))

/-- A block is mixed when it contains both an odd-labelled and an even-labelled entry. -/
def IsMixedBlock {n : ℕ} (b : Finset (ParityIndex n)) : Prop :=
  (∃ i, Sum.inl i ∈ b) ∧ (∃ j, Sum.inr j ∈ b)

/-- Number of odd-even mixed blocks in a parity-labelled set partition. -/
noncomputable def mixedBlockCount {n : ℕ} (P : ParityPartition n) : ℕ := by
  classical
  exact (P.parts.filter IsMixedBlock).card

/-- Partitions of `[n]` having exactly `k` odd-even mixed blocks. -/
abbrev MixedParityPartition (n k : ℕ) :=
  {P : ParityPartition n // mixedBlockCount P = k}

/-- OEIS A124418's `T(n,k)`, defined as the cardinality in its `%N` line. -/
noncomputable def T (n k : ℕ) : ℕ := Fintype.card (MixedParityPartition n k)

/-- The marked blocks carried by a marked partition. -/
abbrev MarkedBlocks {r k : ℕ} (P : MarkedPartition r k) := P.2.1

/-- Restrict to odd and even entries, mark the mixed-derived blocks, and pair their halves. -/
abbrev RestrictionPairingData (n k : ℕ) :=
  Σ odd : MarkedPartition ((n + 1) / 2) k,
    Σ even : MarkedPartition (n / 2) k, MarkedBlocks odd ≃ MarkedBlocks even

/-- The restriction-pairing data have the cardinality on the right side of Hanna's formula. -/
theorem card_restrictionPairingData (n k : ℕ) :
    Fintype.card (RestrictionPairingData n k) =
      k.factorial * A049020 (n / 2) k * A049020 ((n + 1) / 2) k := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  have pairingCard (odd : MarkedPartition ((n + 1) / 2) k)
      (even : MarkedPartition (n / 2) k) :
      Fintype.card (MarkedBlocks odd ≃ MarkedBlocks even) = k.factorial := by
    let e : MarkedBlocks odd ≃ MarkedBlocks even := Fintype.equivOfCardEq (by
      simp only [MarkedBlocks, Fintype.card_coe, odd.2.2, even.2.2])
    rw [Fintype.card_equiv e, Fintype.card_coe, odd.2.2]
  simp_rw [pairingCard]
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul]
  change markedPartitions ((n + 1) / 2) k *
      (markedPartitions (n / 2) k * k.factorial) = _
  rw [markedPartitions_eq_A049020, markedPartitions_eq_A049020]
  ac_rfl

#print axioms markedPartitions_eq_A049020
#print axioms parityIndex_card
#print axioms card_restrictionPairingData

end D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct
