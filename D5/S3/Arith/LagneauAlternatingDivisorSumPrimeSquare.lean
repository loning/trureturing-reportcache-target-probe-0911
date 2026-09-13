/- GID: D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
   generality: G
   mirror-B: D5/B/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A prime alternating sum of decreasing divisors above three forces a square or twice a square. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.LagneauAlternatingDivisorSumPrimeSquare

open scoped ArithmeticFunction

/-- The alternating sum of all divisors of `n`, in nonincreasing order starting with `n`. -/
def T (n : ℕ) : ℤ :=
  ((n.divisors.sort (· ≥ ·)).map fun d ↦ (d : ℤ)).alternatingSum

private theorem alternatingSum_nonneg_of_pairwise_ge :
    ∀ l : List ℕ, l.Pairwise (· ≥ ·) →
      0 ≤ (l.map fun d ↦ (d : ℤ)).alternatingSum
  | [], _ => by simp
  | [a], _ => by simp [List.alternatingSum]
  | a :: b :: l, hsorted => by
      simp only [List.pairwise_cons] at hsorted
      have hab : b ≤ a := hsorted.1 b (by simp)
      have htail : l.Pairwise (· ≥ ·) := hsorted.2.2
      have ih := alternatingSum_nonneg_of_pairwise_ge l htail
      change 0 ≤ (a : ℤ) + -(b : ℤ) + (l.map fun d ↦ (d : ℤ)).alternatingSum
      omega

private theorem le_twice_T (n : ℕ) (hn : 3 < n) : (n : ℤ) ≤ 2 * T n := by
  have hn0 : n ≠ 0 := by omega
  have hsorted :
      n.divisors.sort (· ≥ ·) = n :: n.properDivisors.sort (· ≥ ·) := by
    rw [← Nat.insert_self_properDivisors hn0]
    exact Finset.sort_insert (r := fun a b : ℕ => a ≥ b)
      (fun b hb => (Nat.mem_properDivisors.mp hb).2.le) Nat.self_notMem_properDivisors
  have hproperPairwise :
      (n.properDivisors.sort (· ≥ ·)).Pairwise (· ≥ ·) :=
    Finset.pairwise_sort _ _
  cases hproper : n.properDivisors.sort (· ≥ ·) with
  | nil =>
      have h1 : 1 ∈ n.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨one_dvd n, by omega⟩
      have h1sort : 1 ∈ n.properDivisors.sort (· ≥ ·) :=
        (Finset.mem_sort _).mpr h1
      rw [hproper] at h1sort
      simp at h1sort
  | cons b tail =>
      have hpair : (b :: tail).Pairwise (· ≥ ·) := by
        simpa only [hproper] using hproperPairwise
      have hbSort : b ∈ n.properDivisors.sort (· ≥ ·) := by
        rw [hproper]
        simp
      have hbMem : b ∈ n.properDivisors := (Finset.mem_sort _).mp hbSort
      have hbDiv : b ∣ n := (Nat.mem_properDivisors.mp hbMem).1
      have hbLt : b < n := (Nat.mem_properDivisors.mp hbMem).2
      have hbPos : 0 < b := Nat.pos_of_dvd_of_pos hbDiv (by omega)
      have hquot : 2 ≤ n / b := by
        have hmul : b * (n / b) = n := Nat.mul_div_cancel' hbDiv
        by_contra h
        interval_cases hq : n / b <;> omega
      have htwice : 2 * b ≤ n := by
        calc
          2 * b = b * 2 := by omega
          _ ≤ b * (n / b) := Nat.mul_le_mul_left b hquot
          _ = n := Nat.mul_div_cancel' hbDiv
      have htailNonneg := alternatingSum_nonneg_of_pairwise_ge tail hpair.tail
      rw [T, hsorted, hproper]
      change (n : ℤ) ≤
        2 * ((n : ℤ) + -(b : ℤ) + (tail.map fun d ↦ (d : ℤ)).alternatingSum)
      have htwice' : (2 : ℤ) * b ≤ n := by exact_mod_cast htwice
      omega

private theorem alternatingSum_modEq_sum :
  ∀ l : List ℤ, l.alternatingSum ≡ l.sum [ZMOD 2]
  | [] => Int.ModEq.rfl
  | [a] => by simp [List.alternatingSum]
  | a :: b :: tail => by
      have hb : -b ≡ b [ZMOD 2] := by
        rw [Int.modEq_iff_dvd]
        exact ⟨b, by ring⟩
      have ha : a ≡ a [ZMOD 2] := Int.ModEq.rfl
      simpa only [List.alternatingSum, List.sum_cons, sub_eq_add_neg, neg_sub, add_assoc] using
        (ha.add hb).add (alternatingSum_modEq_sum tail)

end D5.S3.Arith.LagneauAlternatingDivisorSumPrimeSquare
