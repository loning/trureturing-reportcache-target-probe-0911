/- GID: D5/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/PalindromeSquareReversalInfinitude
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: Infinitely many decimal palindromes have nonpalindromic squares whose reversals are squares. -/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

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

/-- Decimal digits of little-endian base-`10^j` blocks, with only the top block unpadded. -/
private def blockDigits (j : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => Nat.digits 10 a
  | a :: b :: rest => Nat.digitsAppend 10 j a ++ blockDigits j (b :: rest)

private theorem digits_of_pow_blocks (j : ℕ) (blocks : List ℕ)
    (hpos : ∀ a ∈ blocks, 0 < a)
    (hlt : ∀ a ∈ blocks, a < 10 ^ j) :
    Nat.digits 10 (Nat.ofDigits (10 ^ j) blocks) = blockDigits j blocks := by
  induction blocks with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => simp [blockDigits, Nat.ofDigits]
      | cons b rest =>
          have hm : 0 < Nat.ofDigits (10 ^ j) (b :: rest) := by
            rw [Nat.ofDigits_cons]
            have hb := hpos b (by simp)
            omega
          have hlen : (Nat.digits 10 a).length ≤ j :=
            (Nat.digits_length_le_iff (by norm_num) a).2 (hlt a (by simp))
          have hadd := Nat.digits_append_zeroes_append_digits
            (b := 10) (k := j - (Nat.digits 10 a).length)
            (m := Nat.ofDigits (10 ^ j) (b :: rest)) (n := a) (by norm_num) hm
          rw [Nat.add_sub_of_le hlen] at hadd
          rw [Nat.ofDigits_cons, ← hadd]
          rw [ih (fun x hx => hpos x (by simp [hx]))
            (fun x hx => hlt x (by simp [hx]))]
          simp only [blockDigits, Nat.digitsAppend, List.append_assoc]

private example (k : ℕ) :
    (blockDigits (k + 5) [1, 11, 90, 110, 100]).reverse =
      blockDigits (k + 5) [1, 11, 90, 110, 100] := by
  let z := List.replicate (k + 4) 0
  have hform :
      blockDigits (k + 5) [1, 11, 90, 110, 100] =
        [1] ++ z ++ [1, 1] ++ z ++ [9] ++ z ++ [1, 1] ++ z ++ [1] := by
    simp [blockDigits, Nat.digitsAppend, z,
      List.replicate_add, List.append_assoc]
  rw [hform]
  simp [z, List.reverse_append, List.reverse_replicate, List.append_assoc]

private example (k : ℕ) :
    (blockDigits (k + 5)
      [1, 22, 301, 2200, 10720, 22000, 30100, 22000, 10000]).reverse =
    blockDigits (k + 5)
      [1, 22, 103, 22, 2701, 220, 10300, 22000, 10000] := by
  let z := List.replicate k 0
  have hpad (n : ℕ) (hn : n < 10 ^ 5) :
      Nat.digitsAppend 10 (k + 5) n = Nat.digitsAppend 10 5 n ++ z := by
    have hlen : (Nat.digits 10 n).length ≤ 5 :=
      (Nat.digits_length_le_iff (by norm_num) n).2 hn
    simp only [Nat.digitsAppend, z]
    rw [show k + 5 - (Nat.digits 10 n).length =
      (5 - (Nat.digits 10 n).length) + k by omega]
    rw [List.replicate_add, List.append_assoc]
  simp only [blockDigits]
  rw [hpad 1 (by norm_num), hpad 22 (by norm_num), hpad 301 (by norm_num),
    hpad 2200 (by norm_num), hpad 10720 (by norm_num), hpad 22000 (by norm_num),
    hpad 30100 (by norm_num), hpad 103 (by norm_num), hpad 2701 (by norm_num),
    hpad 220 (by norm_num), hpad 10300 (by norm_num)]
  simp [Nat.digitsAppend, z, List.reverse_append, List.reverse_replicate,
    List.append_assoc]

end D5.S1.Digit.Admissibility.PalindromeSquareReversalInfinitude
