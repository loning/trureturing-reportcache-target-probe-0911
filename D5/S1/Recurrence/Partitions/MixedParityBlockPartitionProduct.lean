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

private noncomputable def markedValues {α : Type*} [Fintype α] [DecidableEq α]
    {P : Finpartition (univ : Finset α)} (M : Finset P.parts) : Finset (Finset α) :=
  M.image Subtype.val

private noncomputable def gluedSumParts {n k : ℕ} (D : RestrictionPairingData n k) :
    Finset (Finset (ParityIndex n)) :=
  ((D.1.1.parts \ markedValues D.1.2.1).image fun b => b.disjSum ∅) ∪
    (((D.2.1.1.parts \ markedValues D.2.1.2.1).image fun b => (∅ : Finset _).disjSum b) ∪
      D.1.2.1.attach.image fun b => b.1.1.disjSum (D.2.2 b).1.1)

private noncomputable def gluedSumPartition {n k : ℕ} (D : RestrictionPairingData n k) :
    Finpartition (univ : Finset (ParityIndex n)) := by
  classical
  refine Finpartition.ofExistsUnique (gluedSumParts D) (by simp) ?_ ?_
  · intro x _
    cases x with
    | inl a =>
        let ob : D.1.1.parts := ⟨D.1.1.part a, by simp⟩
        by_cases hm : ob ∈ D.1.2.1
        · let block := ob.1.disjSum (D.2.2 ⟨ob, hm⟩).1.1
          refine ⟨block, ⟨?_, by simp [block, ob]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            right
            right
            apply Finset.mem_image.mpr
            exact ⟨⟨ob, hm⟩, by simp, rfl⟩
          · rintro t ⟨ht, hat⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              have hap : a ∈ p := by simpa using hat
              have hpo : p = ob.1 := (D.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hap).symm
              exfalso
              apply (Finset.mem_sdiff.mp hp).2
              apply Finset.mem_image.mpr
              exact ⟨ob, hm, hpo.symm⟩
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              simp at hat
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hap : a ∈ p.1.1 := by simpa using hat
              have hpo : p.1.1 = ob.1 :=
                (D.1.1.part_eq_of_mem p.1.2 hap).symm
              have hpe : p = (⟨ob, hm⟩ : MarkedBlocks D.1) := by
                apply Subtype.ext
                apply Subtype.ext
                exact hpo
              subst p
              rfl
        · let block := ob.1.disjSum (∅ : Finset (Fin (n / 2)))
          refine ⟨block, ⟨?_, by simp [block, ob]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            left
            apply Finset.mem_image.mpr
            exact ⟨ob.1, Finset.mem_sdiff.mpr ⟨ob.2, by
              intro hv
              obtain ⟨p, hp, hpo⟩ := Finset.mem_image.mp hv
              apply hm
              have hpeq : p = ob := Subtype.ext hpo
              simpa [hpeq] using hp⟩, rfl⟩
          · rintro t ⟨ht, hat⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              have hap : a ∈ p := by simpa using hat
              have hpo : p = ob.1 := (D.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hap).symm
              simp [block, hpo]
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              simp at hat
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hap : a ∈ p.1.1 := by simpa using hat
              have hpo : p.1.1 = ob.1 :=
                (D.1.1.part_eq_of_mem p.1.2 hap).symm
              exfalso
              apply hm
              have hpob : p.1 = ob := Subtype.ext hpo
              simpa [hpob] using p.2
    | inr b =>
        let eb : D.2.1.1.parts := ⟨D.2.1.1.part b, by simp⟩
        by_cases hm : eb ∈ D.2.1.2.1
        · let pre : MarkedBlocks D.1 := D.2.2.symm ⟨eb, hm⟩
          let block := pre.1.1.disjSum eb.1
          refine ⟨block, ⟨?_, by simp [block, eb]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            right
            right
            apply Finset.mem_image.mpr
            exact ⟨pre, by simp, by simp [block, pre]⟩
          · rintro t ⟨ht, hbt⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              simp at hbt
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              have hbp : b ∈ p := by simpa using hbt
              have hpe : p = eb.1 := (D.2.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hbp).symm
              exfalso
              apply (Finset.mem_sdiff.mp hp).2
              apply Finset.mem_image.mpr
              exact ⟨eb, hm, hpe.symm⟩
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hbp : b ∈ (D.2.2 p).1.1 := by simpa using hbt
              have hpe : (D.2.2 p).1.1 = eb.1 :=
                (D.2.1.1.part_eq_of_mem (D.2.2 p).1.2 hbp).symm
              have hpeq : D.2.2 p = (⟨eb, hm⟩ : MarkedBlocks D.2.1) := by
                apply Subtype.ext
                apply Subtype.ext
                exact hpe
              have hp : p = pre := by
                apply D.2.2.injective
                simpa [pre] using hpeq
              subst p
              simp [block, pre]
        · let block := (∅ : Finset (Fin ((n + 1) / 2))).disjSum eb.1
          refine ⟨block, ⟨?_, by simp [block, eb]⟩, ?_⟩
          · simp only [gluedSumParts, Finset.mem_union]
            right
            left
            apply Finset.mem_image.mpr
            exact ⟨eb.1, Finset.mem_sdiff.mpr ⟨eb.2, by
              intro hv
              obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hv
              apply hm
              have hpeq : p = eb := Subtype.ext hpe
              simpa [hpeq] using hp⟩, rfl⟩
          · rintro t ⟨ht, hbt⟩
            simp only [gluedSumParts, Finset.mem_union] at ht
            rcases ht with hodd | heven | hmixed
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hodd
              simp at hbt
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heven
              have hbp : b ∈ p := by simpa using hbt
              have hpe : p = eb.1 := (D.2.1.1.part_eq_of_mem (Finset.mem_sdiff.mp hp).1 hbp).symm
              simp [block, hpe]
            · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmixed
              subst t
              have hbp : b ∈ (D.2.2 p).1.1 := by simpa using hbt
              have hpe : (D.2.2 p).1.1 = eb.1 :=
                (D.2.1.1.part_eq_of_mem (D.2.2 p).1.2 hbp).symm
              exfalso
              apply hm
              have heq : (D.2.2 p).1 = eb := Subtype.ext hpe
              simpa [heq] using (D.2.2 p).2
  · simp only [gluedSumParts, Finset.mem_union]
    rintro h
    rcases h with hodd | heven | hmixed
    · obtain ⟨p, hp, h⟩ := Finset.mem_image.mp hodd
      have hpe : p = ∅ := (Finset.disjSum_eq_empty.mp h).1
      have hempty : (∅ : Finset (Fin ((n + 1) / 2))) ∈ D.1.1.parts := by
        rw [← hpe]
        exact (Finset.mem_sdiff.mp hp).1
      exact D.1.1.bot_notMem hempty

    · obtain ⟨p, hp, h⟩ := Finset.mem_image.mp heven
      have hpe : p = ∅ := (Finset.disjSum_eq_empty.mp h).2
      have hempty : (∅ : Finset (Fin (n / 2))) ∈ D.2.1.1.parts := by
        rw [← hpe]
        exact (Finset.mem_sdiff.mp hp).1
      exact D.2.1.1.bot_notMem hempty
    · obtain ⟨p, hp, h⟩ := Finset.mem_image.mp hmixed
      have hpe : p.1.1 = ∅ := (Finset.disjSum_eq_empty.mp h).1
      have hempty : (∅ : Finset (Fin ((n + 1) / 2))) ∈ D.1.1.parts := by
        rw [← hpe]
        exact p.1.2
      exact D.1.1.bot_notMem hempty

private noncomputable def gluedPartition {n k : ℕ} (D : RestrictionPairingData n k) :
    ParityPartition n :=
  ((gluedSumPartition D).map Finset.sumEquiv).copy (by
    apply Prod.ext <;> simp)

private noncomputable def gluedMixedEmbedding {n k : ℕ}
    (D : RestrictionPairingData n k) : MarkedBlocks D.1 ↪ ParityBlock n where
  toFun b := (b.1.1, (D.2.2 b).1.1)
  inj' := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Prod.fst h

private noncomputable def gluedMixedPartition {n k : ℕ}
    (D : RestrictionPairingData n k) : MixedParityPartition n k := by
  classical
  refine ⟨gluedPartition D, ?_⟩
  rw [mixedBlockCount]
  have hparts : (gluedPartition D).parts.filter IsMixedBlock =
      D.1.2.1.attach.map (gluedMixedEmbedding D) := by
    ext p
    simp only [gluedPartition, Finpartition.copy_parts, Finpartition.parts_map,
      Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨b, hb, hbp⟩, hp⟩
      subst p
      simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts] at hb
      simp only [gluedSumParts, Finset.mem_union] at hb
      rcases hb with hodd | heven | hmixed
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hodd
        have hp' := hp.2
        change (a.disjSum (∅ : Finset (Fin (n / 2)))).toRight.Nonempty at hp'
        rw [Finset.toRight_disjSum] at hp'
        exact (Finset.not_nonempty_empty hp').elim
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp heven
        have hp' := hp.1
        change ((∅ : Finset (Fin ((n + 1) / 2))).disjSum a).toLeft.Nonempty at hp'
        rw [Finset.toLeft_disjSum] at hp'
        exact (Finset.not_nonempty_empty hp').elim
      · obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hmixed
        subst b
        refine ⟨a, by simp, ?_⟩
        apply Prod.ext
        · change a.1.1 = (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).1
          simp
        · change (D.2.2 a).1.1 = (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).2
          simp
    · rintro ⟨a, ha, hap⟩
      subst p
      refine ⟨?_, ?_⟩
      · refine ⟨a.1.1.disjSum (D.2.2 a).1.1, ?_, ?_⟩
        · simp only [gluedSumPartition, Finpartition.ofExistsUnique_parts, gluedSumParts,
            Finset.mem_union]
          right
          right
          exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩
        · apply Prod.ext
          · change (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).1 = a.1.1
            simp
          · change (Finset.sumEquiv (a.1.1.disjSum (D.2.2 a).1.1)).2 = (D.2.2 a).1.1
            simp
      · exact ⟨D.1.1.nonempty_of_mem_parts a.1.2,
          D.2.1.1.nonempty_of_mem_parts (D.2.2 a).1.2⟩
  rw [hparts, Finset.card_map, Finset.card_attach]
  exact D.1.2.2

#print axioms markedPartitions_eq_A049020

end D5.S1.Recurrence.Partitions.MixedParityBlockPartitionProduct
