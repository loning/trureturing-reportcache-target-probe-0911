/- GID: D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   generality: G
   mirror-B: D5/B/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Order.Partition.Finpartition, Mathlib.Data.Fintype.Powerset, Mathlib.Data.Fintype.Sigma, Mathlib.Data.Fintype.BigOperators, Mathlib.Data.Finset.Sum]
   utility: none
   digest: Marked set partitions and the odd-even mixed-block product conjecture. -/

import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sum

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

/-- A block after transporting along `Finset.sumEquiv`: its two coordinates are the
odd and even restrictions of the original block. -/
abbrev ParityBlock (n : ℕ) :=
  Finset (Fin ((n + 1) / 2)) × Finset (Fin (n / 2))

/-- Set partitions of the parity-labelled `n`-element set, transported along
`Finset.sumEquiv` to the product lattice of odd and even subsets. -/
abbrev ParityPartition (n : ℕ) :=
  Finpartition ((univ : Finset (Fin ((n + 1) / 2))), (univ : Finset (Fin (n / 2))))

/-- A block is mixed when it contains both an odd-labelled and an even-labelled entry. -/
def IsMixedBlock {n : ℕ} (b : ParityBlock n) : Prop :=
  b.1.Nonempty ∧ b.2.Nonempty

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

private noncomputable def leftRestriction {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    Finpartition (univ : Finset α) := by
  refine Finpartition.ofExistsUnique
    ((P.parts.image Prod.fst).erase ∅) (by simp) ?_ (by simp)
  intro a _
  have hsup : P.parts.sup Prod.fst = (univ : Finset α) := by
    simpa using P.sup_parts_apply (fun _ _ => rfl) rfl
  have ha : a ∈ P.parts.sup Prod.fst := by simp [hsup]
  obtain ⟨q, hq, haq⟩ := Finset.mem_sup.mp ha
  refine ⟨q.1, ⟨Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp ⟨a, haq⟩,
    Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩, haq⟩, ?_⟩
  rintro t ⟨ht, hat⟩
  have htimage : t ∈ P.parts.image Prod.fst := (Finset.mem_erase.mp ht).2
  obtain ⟨r, hr, hrt⟩ := Finset.mem_image.mp htimage
  subst t
  have hqr : q = r := by
    by_contra hne
    have hd := P.disjoint hq hr hne
    change Disjoint q r at hd
    rw [Prod.disjoint_iff] at hd
    exact (Finset.not_disjoint_iff.mpr ⟨a, haq, hat⟩) hd.1
  exact (congrArg Prod.fst hqr).symm

private noncomputable def rightRestriction {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    Finpartition (univ : Finset β) := by
  refine Finpartition.ofExistsUnique
    ((P.parts.image Prod.snd).erase ∅) (by simp) ?_ (by simp)
  intro b _
  have hsup : P.parts.sup Prod.snd = (univ : Finset β) := by
    simpa using P.sup_parts_apply (fun _ _ => rfl) rfl
  have hb : b ∈ P.parts.sup Prod.snd := by simp [hsup]
  obtain ⟨q, hq, hbq⟩ := Finset.mem_sup.mp hb
  refine ⟨q.2, ⟨Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp ⟨b, hbq⟩,
    Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩, hbq⟩, ?_⟩
  rintro t ⟨ht, hbt⟩
  have htimage : t ∈ P.parts.image Prod.snd := (Finset.mem_erase.mp ht).2
  obtain ⟨r, hr, hrt⟩ := Finset.mem_image.mp htimage
  subst t
  have hqr : q = r := by
    by_contra hne
    have hd := P.disjoint hq hr hne
    change Disjoint q r at hd
    rw [Prod.disjoint_iff] at hd
    exact (Finset.not_disjoint_iff.mpr ⟨b, hbq, hbt⟩) hd.2
  exact (congrArg Prod.snd hqr).symm

private def mixedParts {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (P : Finpartition (s, t)) :
    Finset (Finset α × Finset β) :=
  P.parts.filter fun p => p.1.Nonempty ∧ p.2.Nonempty

private noncomputable def mixedToLeftEmbedding {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    {p // p ∈ mixedParts P} ↪ (leftRestriction P).parts where
  toFun p := ⟨p.1.1, by
    change p.1.1 ∈ (P.parts.image Prod.fst).erase ∅
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp p.2).2.1.ne_empty,
      Finset.mem_image.mpr ⟨p.1, (Finset.mem_filter.mp p.2).1, rfl⟩⟩⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hpq : p.1.1 = q.1.1 := congrArg Subtype.val h
    by_contra hpq'
    have hd := P.disjoint (Finset.mem_filter.mp p.2).1
      (Finset.mem_filter.mp q.2).1 hpq'
    change Disjoint p.1 q.1 at hd
    rw [Prod.disjoint_iff] at hd
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp p.2).2.1
    exact (Finset.not_disjoint_iff.mpr ⟨a, ha, hpq ▸ ha⟩) hd.1

private noncomputable def mixedToRightEmbedding {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    {p // p ∈ mixedParts P} ↪ (rightRestriction P).parts where
  toFun p := ⟨p.1.2, by
    change p.1.2 ∈ (P.parts.image Prod.snd).erase ∅
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp p.2).2.2.ne_empty,
      Finset.mem_image.mpr ⟨p.1, (Finset.mem_filter.mp p.2).1, rfl⟩⟩⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hpq : p.1.2 = q.1.2 := congrArg Subtype.val h
    by_contra hpq'
    have hd := P.disjoint (Finset.mem_filter.mp p.2).1
      (Finset.mem_filter.mp q.2).1 hpq'
    change Disjoint p.1 q.1 at hd
    rw [Prod.disjoint_iff] at hd
    obtain ⟨b, hb⟩ := (Finset.mem_filter.mp p.2).2.2
    exact (Finset.not_disjoint_iff.mpr ⟨b, hb, hpq ▸ hb⟩) hd.2

private noncomputable def leftMarkedParts {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    Finset (leftRestriction P).parts :=
  (mixedParts P).attach.map (mixedToLeftEmbedding P)

private noncomputable def rightMarkedParts {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    Finset (rightRestriction P).parts :=
  (mixedParts P).attach.map (mixedToRightEmbedding P)

private noncomputable def mixedLeftEquiv {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    {p // p ∈ mixedParts P} ≃ {b // b ∈ leftMarkedParts P} :=
  Equiv.ofBijective
    (fun p => ⟨mixedToLeftEmbedding P p, by simp [leftMarkedParts]⟩)
    ⟨fun _ _ h => (mixedToLeftEmbedding P).injective (congrArg Subtype.val h), by
      intro b
      obtain ⟨p, hp, hpb⟩ := Finset.mem_map.mp b.2
      exact ⟨p, Subtype.ext hpb⟩⟩

private noncomputable def mixedRightEquiv {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition ((univ : Finset α), (univ : Finset β))) :
    {p // p ∈ mixedParts P} ≃ {b // b ∈ rightMarkedParts P} :=
  Equiv.ofBijective
    (fun p => ⟨mixedToRightEmbedding P p, by simp [rightMarkedParts]⟩)
    ⟨fun _ _ h => (mixedToRightEmbedding P).injective (congrArg Subtype.val h), by
      intro b
      obtain ⟨p, hp, hpb⟩ := Finset.mem_map.mp b.2
      exact ⟨p, Subtype.ext hpb⟩⟩

private noncomputable def leftMarkedPartition {n k : ℕ}
    (P : MixedParityPartition n k) : MarkedPartition ((n + 1) / 2) k := by
  classical
  refine ⟨leftRestriction P.1, leftMarkedParts P.1, ?_⟩
  ·
    rw [leftMarkedParts, Finset.card_map, Finset.card_attach]
    have hm : mixedParts P.1 = P.1.parts.filter IsMixedBlock := by
      ext p
      simp only [mixedParts, Finset.mem_filter]
      change (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty) ↔
        (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty)
      rfl
    rw [hm]
    exact P.2

private noncomputable def rightMarkedPartition {n k : ℕ}
    (P : MixedParityPartition n k) : MarkedPartition (n / 2) k := by
  classical
  refine ⟨rightRestriction P.1, rightMarkedParts P.1, ?_⟩
  ·
    rw [rightMarkedParts, Finset.card_map, Finset.card_attach]
    have hm : mixedParts P.1 = P.1.parts.filter IsMixedBlock := by
      ext p
      simp only [mixedParts, Finset.mem_filter]
      change (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty) ↔
        (p ∈ P.1.parts ∧ p.1.Nonempty ∧ p.2.Nonempty)
      rfl
    rw [hm]
    exact P.2

private noncomputable def restrictionData {n k : ℕ}
    (P : MixedParityPartition n k) : RestrictionPairingData n k :=
  ⟨leftMarkedPartition P, rightMarkedPartition P,
    (mixedLeftEquiv P.1).symm.trans (mixedRightEquiv P.1)⟩

#print axioms markedPartitions_eq_A049020

end D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct
