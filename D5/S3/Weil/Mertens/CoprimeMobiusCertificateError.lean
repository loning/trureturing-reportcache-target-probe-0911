/- GID: D5/S3/Weil/Mertens/CoprimeMobiusCertificateError
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CoprimeMobiusCertificateError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the uniform error of the coprime truncated Mobius certificate. -/

import D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open scoped BigOperators
open Finset
open private divisorList from D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

noncomputable section
namespace D5.S3.Weil.Mertens.CoprimeMobiusCertificateError

/-- The Mobius sum over positive divisors up to an inclusive real endpoint. -/
def B (R : ℕ) (u : ℝ) : ℤ :=
  ∑ a ∈ R.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u), ArithmeticFunction.moebius a

/-- The number of positive integers at most a real endpoint and coprime to the modulus. -/
def C (R : ℕ) (x : ℝ) : ℝ :=
  ((Icc 1 ⌊x⌋₊).filter (fun d => d.Coprime R)).card

/-- The sum of absolute truncated kernels over all positive coprime integers up to N. -/
def U (R N : ℕ) : ℝ := if R = 1 then N else
  ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime R), |(B R ((N : ℝ) / d) : ℝ)|

/-- Consecutive pairs in the increasing list of positive divisors. -/
def pairs (R : ℕ) : List (ℕ × ℕ) :=
  (divisorList R).zip (divisorList R).tail

/-- The total absolute partial Mobius sum over the bounded divisor intervals. -/
def mass (R : ℕ) : ℝ := ((pairs R).map (fun ab => |(B R ab.1 : ℝ)|)).sum

/-- The density of integers coprime to the modulus. -/
def e (R : ℕ) : ℝ := (R.totient : ℝ) / R

/-- The linear coefficient obtained from the actual consecutive divisor intervals. -/
def c (R : ℕ) : ℝ := if R = 1 then 1 else
  e R * ((pairs R).map (fun ab => |(B R ab.1 : ℝ)| *
    ((ab.1 : ℝ)⁻¹ - (ab.2 : ℝ)⁻¹))).sum

end D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
