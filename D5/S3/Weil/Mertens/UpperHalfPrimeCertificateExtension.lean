/- GID: D5/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjoining omitted upper-half primes gives the same exact change in both Mobius certificates. -/

import D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Weil.Mertens.CoprimeMobiusCertificateError

noncomputable section
namespace D5.S3.Weil.Mertens.UpperHalfPrimeCertificateExtension

/-- The absolute truncated Mobius kernels summed over positive squarefree coprime indices. -/
def W (Q N : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime Q ∧ Squarefree d),
    |(B Q ((N : ℝ) / d) : ℝ)|

/-- Adjoining any finite set of omitted primes in the upper half of the window changes
both absolute Mobius certificates by the same cardinality and endpoint-kernel expression. -/
theorem certificate_extension (Q N : ℕ) (T : Finset ℕ)
    (hQ : Squarefree Q) (hQ1 : 1 ≤ Q) (hN : 2 ≤ N)
    (hT : ∀ p ∈ T, p.Prime ∧ N < 2 * p ∧ p ≤ N ∧ ¬ p ∣ Q) :
    let R := ∏ p ∈ T, p
    let delta : ℝ := T.card + |(B Q N : ℝ)| - |(B Q N : ℝ) - T.card|
    U Q N - U (Q * R) N = delta ∧ W Q N - W (Q * R) N = delta := by
  classical
  sorry

end D5.S3.Weil.Mertens.UpperHalfPrimeCertificateExtension
