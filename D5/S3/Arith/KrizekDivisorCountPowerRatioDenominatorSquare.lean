/- GID: D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare
   generality: G
   mirror-B: D5/B/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.Data.Rat.Lemmas, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: OEIS A302975: every reduced denominator of tau(n)^n / n^tau(n) is a square. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.KrizekDivisorCountPowerRatioDenominatorSquare

/-- The reduced denominator of `tau(n)^n / n^tau(n)`, as in OEIS A302975.
At `n = 0` this definition has the totalized value `1`; the source claim starts at `n = 1`. -/
def D (n : ℕ) : ℕ :=
  (((Nat.divisors n).card : ℚ) ^ n /
    (n : ℚ) ^ (Nat.divisors n).card).den

private theorem D_factorization (n p : ℕ) (hn : 1 ≤ n) :
    (D n).factorization p =
      (Nat.divisors n).card * n.factorization p -
        n * (Nat.divisors n).card.factorization p := by
  let t := (Nat.divisors n).card
  let a := t ^ n
  let b := n ^ t
  let g := Nat.gcd a b
  have hn0 : n ≠ 0 := by omega
  have ht0 : t ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
  have hb : 0 < b := Nat.pow_pos (by omega)
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
  have hq : (a : ℚ) / (b : ℚ) =
      ((a / g : ℕ) : ℚ) / ((b / g : ℕ) : ℚ) := by
    rw [Nat.cast_div (Nat.gcd_dvd_left a b) (by exact_mod_cast hg.ne'),
      Nat.cast_div (Nat.gcd_dvd_right a b) (by exact_mod_cast hg.ne')]
    exact (div_div_div_cancel_right₀ (by exact_mod_cast hg.ne') (a : ℚ) (b : ℚ)).symm
  have hcoprime : Nat.Coprime (a / g) (b / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hgb : g ≤ b := Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)
  have hbq : 0 < b / g := Nat.div_pos hgb hg
  have hdenInt := Rat.den_div_eq_of_coprime
    (a := ((a / g : ℕ) : ℤ)) (b := ((b / g : ℕ) : ℤ))
    (by exact_mod_cast hbq)
    (by simpa only [Int.natAbs_natCast] using hcoprime)
  change (((((a / g : ℕ) : ℚ) / ((b / g : ℕ) : ℚ)).den : ℤ) =
    ((b / g : ℕ) : ℤ)) at hdenInt
  have hden : (((a : ℚ) / (b : ℚ)).den) = b / g := by
    rw [hq]
    exact_mod_cast hdenInt
  have hD : D n = b / g := by
    unfold D
    simpa only [a, b, t, Nat.cast_pow] using hden
  rw [hD, Nat.factorization_div (Nat.gcd_dvd_right _ _),
    Nat.factorization_gcd (pow_ne_zero _ ht0) (pow_ne_zero _ hn0)]
  simp only [b, t, Nat.factorization_pow, Finsupp.coe_tsub, Pi.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.inf_apply]
  rw [min_comm, tsub_min]

private theorem factorization_even_of_card_divisors_odd
    (n p : ℕ) (hn : n ≠ 0) (ht : Odd (Nat.divisors n).card) :
    Even (n.factorization p) := by
  by_cases hp : p ∈ n.primeFactors
  · rw [Nat.card_divisors hn] at ht
    by_contra heven
    have hoddExp : Odd (n.factorization p) := Nat.not_even_iff_odd.mp heven
    have hfactorEven : Even (n.factorization p + 1) := hoddExp.add_one
    have hfactorDvd : n.factorization p + 1 ∣
        ∏ q ∈ n.primeFactors, (n.factorization q + 1) :=
      Finset.dvd_prod_of_mem (fun q => n.factorization q + 1) hp
    have hprodEven : Even (∏ q ∈ n.primeFactors, (n.factorization q + 1)) :=
      even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hfactorEven).trans hfactorDvd)
    exact (Nat.not_even_iff_odd.mpr ht) hprodEven
  · have hz : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    simp [hz]

private theorem card_divisors_mul_factorization_le_of_odd
    (n p : ℕ) (hn : Odd n) :
    (Nat.divisors n).card * n.factorization p ≤ n := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  by_cases hp : p ∈ n.primeFactors
  · have hprime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    have hnotTwoDvd : ¬2 ∣ n := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hn)
    have hpNeTwo : p ≠ 2 := by
      intro h
      exact hnotTwoDvd (h ▸ hpDvd)
    have hpThree : 3 ≤ p := by
      have := hprime.two_le
      omega
    have hePos : 0 < n.factorization p := by
      apply Nat.pos_of_ne_zero
      apply Finsupp.mem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    have hcube : n.factorization p * (n.factorization p + 1) ≤
        3 ^ n.factorization p := by
      generalize n.factorization p = e at hePos ⊢
      induction e with
      | zero => omega
      | succ e ih =>
          by_cases hz : e = 0
          · subst e
            norm_num
          · have ih' : e * (e + 1) ≤ 3 ^ e := ih (by omega)
            rw [pow_succ]
            calc
              (e + 1) * (e + 1 + 1) ≤ (e + 1) * (3 * e) :=
                Nat.mul_le_mul_left (e + 1) (by omega)
              _ = 3 * (e * (e + 1)) := by ring
              _ ≤ 3 * 3 ^ e := Nat.mul_le_mul_left 3 ih'
              _ = 3 ^ e * 3 := by omega
    have hspecial : (n.factorization p + 1) * n.factorization p ≤
        p ^ n.factorization p := by
      rw [mul_comm]
      exact hcube.trans (Nat.pow_le_pow_left hpThree _)
    have hrest :
        (∏ q ∈ n.primeFactors.erase p, (n.factorization q + 1)) ≤
          ∏ q ∈ n.primeFactors.erase p, q ^ n.factorization q := by
      apply Finset.prod_le_prod
      · simp
      · intro q hq
        have hqMem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
        have hqPrime := Nat.prime_of_mem_primeFactors hqMem
        have hqTwo : 2 ≤ q := hqPrime.two_le
        have hlinear := one_add_le_pow_of_two_add_nonneg
          (R := ℕ) (a := q - 1) (by omega) (n.factorization q)
        have hbase : 1 + (q - 1) = q := by omega
        rw [hbase] at hlinear
        have hqsub : 1 ≤ q - 1 := by omega
        have hmul : n.factorization q ≤ n.factorization q * (q - 1) := by
          simpa using Nat.mul_le_mul_left (n.factorization q) hqsub
        have hadd : n.factorization q + 1 ≤
            1 + n.factorization q * (q - 1) := by
          simpa [add_comm] using Nat.add_le_add_right hmul 1
        exact hadd.trans hlinear
    rw [Nat.card_divisors hn0]
    calc
      (∏ q ∈ n.primeFactors, (n.factorization q + 1)) * n.factorization p =
          ((n.factorization p + 1) * n.factorization p) *
            ∏ q ∈ n.primeFactors.erase p, (n.factorization q + 1) := by
              rw [← Finset.mul_prod_erase n.primeFactors
                (fun q => n.factorization q + 1) hp]
              ring
      _ ≤ p ^ n.factorization p *
          ∏ q ∈ n.primeFactors.erase p, q ^ n.factorization q :=
        Nat.mul_le_mul hspecial hrest
      _ = ∏ q ∈ n.primeFactors, q ^ n.factorization q :=
        Finset.mul_prod_erase n.primeFactors (fun q => q ^ n.factorization q) hp
      _ = n := (Nat.prod_primeFactors_pow_factorization hn0).symm
  · have hz : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    simp [hz]

end D5.S3.Arith.KrizekDivisorCountPowerRatioDenominatorSquare
