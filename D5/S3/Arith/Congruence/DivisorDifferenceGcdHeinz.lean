/- GID: D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.NumberTheory.PrimeCounting, mathlib/module/Mathlib.Data.Nat.Factorization.Basic]
   utility: none
   digest: Wiseman's A258409 divisor-minus-one gcd equals the consecutive divisor-gap gcd and its Heinz prime-index gcd.
 -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

noncomputable def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

noncomputable def consecutiveDivisorDifferences (n : ℕ) : List ℕ :=
  (divisorList n).zipWith (fun x y => y - x) (divisorList n).tail

def a (n : ℕ) : ℕ := n.divisors.gcd (fun d => d - 1)

noncomputable def consecutiveDifferenceGcd (n : ℕ) : ℕ :=
  (consecutiveDivisorDifferences n).toFinset.gcd id

noncomputable def heinzDifferences (n : ℕ) : ℕ :=
  ((consecutiveDivisorDifferences n).map (fun d => Nat.nth Nat.Prime (d - 1))).prod

noncomputable def primeIndexGcd (m : ℕ) : ℕ := m.primeFactors.gcd Nat.primeCounting

private theorem dvd_sub_base_of_dvd_gaps (a : ℕ) :
    ∀ (rest : List ℕ), (a :: rest).Pairwise (· ≤ ·) → ∀ k : ℕ,
      (∀ d ∈ (a :: rest).zipWith (fun x y => y - x) (a :: rest).tail, k ∣ d) →
        ∀ x ∈ a :: rest, k ∣ x - a := by
  intro rest
  revert a
  induction rest with
  | nil =>
      intro a _ k hg x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      simp
  | cons b bs ih =>
      intro a hs k hg x hx
      have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
      have hgap : k ∣ b - a := by
        apply hg
        simp
      have htail : (b :: bs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      have hgap_tail : ∀ d ∈ (b :: bs).zipWith (fun x y => y - x) (b :: bs).tail, k ∣ d := by
        intro d hd
        apply hg
        simp only [List.zipWith, List.tail, List.mem_cons]
        exact Or.inr hd
      have ih' := ih b htail k hgap_tail
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x
        simp
      · have hx' : x ∈ b :: bs := by simpa [hx]
        have hxb : k ∣ x - b := ih' x hx'
        have hbx : b ≤ x := by
          have hx'' : x = b ∨ x ∈ bs := by simpa only [List.mem_cons] using hx'
          rcases hx'' with rfl | hx''
          · exact le_rfl
          · exact (List.pairwise_cons.mp htail).1 x hx''
        rw [← Nat.sub_add_sub_cancel hbx hab]
        exact Nat.dvd_add hxb hgap

private theorem dvd_gaps_of_dvd_sub_base :
    ∀ (a : ℕ) (l : List ℕ) (k : ℕ),
      l.Pairwise (· ≤ ·) →
      (∀ x ∈ l, a ≤ x) →
      (∀ x ∈ l, k ∣ x - a) →
        ∀ d ∈ l.zipWith (fun x y => y - x) l.tail, k ∣ d := by
  intro a l
  induction l with
  | nil =>
      intro k _ _ _ d hd
      simp at hd
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro k _ _ _ d hd
          simp at hd
      | cons y ys =>
          intro k hs hbase hoff d hd
          have hax : a ≤ x := hbase x (by simp)
          have hxy : x ≤ y := (List.pairwise_cons.mp hs).1 y (by simp)
          have hfirst0 : k ∣ (y - a) - (x - a) :=
            Nat.dvd_sub (hoff y (by simp)) (hoff x (by simp))
          have hfirst : k ∣ y - x := by
            have heq : (y - a) - (x - a) = y - x := by omega
            exact heq ▸ hfirst0
          have htail_dvd : ∀ e ∈ (y :: ys).zipWith (fun u v => v - u) (y :: ys).tail, k ∣ e :=
            ih k (List.pairwise_cons.mp hs).2 (by
              intro z hz
              exact hbase z (by simp [hz])) (by
              intro z hz
              exact hoff z (by simp [hz]))
          simp only [List.zipWith, List.tail, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hfirst
          · exact htail_dvd d hd

private theorem sorted_list_gcd_sub_one_eq_gaps
    (rest : List ℕ) (hs : (1 :: rest).Pairwise (· ≤ ·)) :
    (1 :: rest).toFinset.gcd (fun d => d - 1) =
      ((1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail).toFinset.gcd id := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro d hd
    have hd' : d ∈ (1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail := by
      simpa using hd
    have hoff : ∀ x ∈ 1 :: rest, (1 :: rest).toFinset.gcd (fun d => d - 1) ∣ x - 1 := by
      intro x hx
      exact Finset.gcd_dvd (by simpa using hx)
    have hbase : ∀ x ∈ 1 :: rest, 1 ≤ x := by
      intro x hx
      have hx' : x = 1 ∨ x ∈ rest := by simpa only [List.mem_cons] using hx
      rcases hx' with hx' | hx'
      · simpa [hx']
      · exact (List.pairwise_cons.mp hs).1 x hx'
    exact dvd_gaps_of_dvd_sub_base 1 (1 :: rest) _ hs hbase hoff d hd'
  · apply Finset.dvd_gcd
    intro d hd
    have hgap : ∀ e ∈ (1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail,
        ((1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail).toFinset.gcd id ∣ e := by
      intro e he
      exact Finset.gcd_dvd (by simpa using he)
    have hoff := dvd_sub_base_of_dvd_gaps 1 rest hs _ hgap
    exact hoff d (by simpa using hd)

theorem wiseman_a258409 : ∀ n, 2 ≤ n →
    a n = primeIndexGcd (heinzDifferences n) ∧
      a n = consecutiveDifferenceGcd n := by
  intro n hn
  sorry

end D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz
