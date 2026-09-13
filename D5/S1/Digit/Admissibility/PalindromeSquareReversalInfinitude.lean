/- GID: D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: Infinitely many decimal palindromes have nonpalindromic squares whose reversals are squares. -/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Palindromes whose reversed square is a square

`Nat.digits` is little-endian. Thus reversing that list and applying
`Nat.ofDigits` gives the natural number obtained by reversing the usual
decimal representation. This is distinct from
`D5.S3.Arith.SumInConcatenation.D`, which returns only a digit list.
-/

namespace D5.S1.Digit.Admissibility.PalindromeSquareReversalInfinitude

/-- Reverse the ordinary base-ten digits of a natural number. -/
def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- A natural number is a decimal palindrome. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  rev10 n = n

/-- Membership in OEIS A133901, expressed through the definition of A128921. -/
def IsMember (p : ℕ) : Prop :=
  IsPalindrome10 p ∧ ¬ IsPalindrome10 (p ^ 2) ∧ ∃ q, rev10 (p ^ 2) = q ^ 2

#eval rev10 1252409430321

private example : IsMember 33 := by
  constructor
  · change rev10 33 = 33
    decide
  constructor
  · change ¬rev10 (33 ^ 2) = 33 ^ 2
    decide
  · exact ⟨99, by decide⟩

end D5.S1.Digit.Admissibility.PalindromeSquareReversalInfinitude
