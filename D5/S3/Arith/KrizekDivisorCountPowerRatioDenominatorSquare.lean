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

end D5.S3.Arith.KrizekDivisorCountPowerRatioDenominatorSquare
