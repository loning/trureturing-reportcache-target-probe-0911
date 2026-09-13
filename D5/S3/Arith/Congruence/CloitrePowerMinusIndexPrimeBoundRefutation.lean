/- GID: D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Data.Nat.Prime.Nth, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.claim; result=D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.result; claim=D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.claim
   digest: The n = 6298 certificate refutes Cloitre's A072872 prime-index upper bound. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.CloitrePowerMinusIndexPrimeBoundRefutation

/-!
OEIS A072872 defines `a(n)` as "the smallest positive number k such that n
divides 2^k - k." Benoit Cloitre's comment of 2002-07-28 conjectures:
"If n is a power of 2, a(n) = n. Conjecture : if n > 47, a(n) < prime(n)."

The infimum convention below returns zero when the defining set is empty; no
general existence assertion is made here. The OEIS offset is one, so
`prime(n)` is represented by `Nat.nth Nat.Prime (n - 1)`.

At `n = 6298`, a verified modular recurrence checks every positive exponent
below 77742 and verifies the endpoint, while an independent bounded trial
division checker certifies that exactly 6297 primes precede the prime 62753.
Thus `a(6298) = 77742 > 62753 = prime(6298)`.
-/

/-- The literal A072872 sequence definition. If the defining set is empty,
the natural-number `sInf` convention gives zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ n ∣ 2 ^ k - k}

/-- Cloitre's literal prime-index upper-bound conjecture from A072872. -/
def claim : Prop :=
  ∀ n : ℕ, 47 < n → a n < Nat.nth Nat.Prime (n - 1)

private def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range 249).all fun i => decide (i + 2 < n → ¬(i + 2) ∣ n)

private def trialCount (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 =>
      trialCount start len + if trialPrime (start + len) then 1 else 0

private theorem trialPrime_iff_prime {n : ℕ} (hn : n < 62753) :
    trialPrime n = true ↔ Nat.Prime n := by
  have hshape :
      trialPrime n = true ↔
        2 ≤ n ∧ ∀ i, i < 249 → i + 2 < n → ¬(i + 2) ∣ n := by
    simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
  rw [hshape]
  constructor
  · rintro ⟨hn2, htrial⟩
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hn2, fun m hm hmsqrt => ?_⟩
    have hm250 : m ≤ 250 := by
      have hsqrt : Nat.sqrt n < 251 := Nat.sqrt_lt.mpr (hn.trans (by decide))
      omega
    have hindex : m - 2 < 249 := by omega
    have hm_lt : m < n := hmsqrt.trans_lt (Nat.sqrt_lt_self hn2)
    have hres := htrial (m - 2) hindex (by omega)
    simpa only [Nat.sub_add_cancel hm] using hres
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro i _ hdlt hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · have hilower : 2 ≤ i + 2 := by omega
      exact (not_lt_of_ge hilower) (h ▸ by decide)
    · exact (ne_of_lt hdlt) h

private theorem count_add_trialCount (start len : ℕ)
    (hbound : start + len ≤ 62753) :
    Nat.count Nat.Prime (start + len) =
      Nat.count Nat.Prime start + trialCount start len := by
  induction len with
  | zero => simp [trialCount]
  | succ len ih =>
      rw [Nat.add_succ, Nat.count_succ, trialCount, ih (by omega)]
      by_cases hp : Nat.Prime (start + len)
      · have ht : trialPrime (start + len) = true :=
          (trialPrime_iff_prime (by omega)).2 hp
        simp [hp, ht, Nat.add_assoc]
      · have ht : trialPrime (start + len) ≠ true := fun h =>
          hp ((trialPrime_iff_prime (by omega)).1 h)
        simp [hp, ht]

private def advance : ℕ → ℕ → ℕ
  | r, 0 => r
  | r, len + 1 => advance ((2 * r) % 6298) len

private def scan : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | k, r, len + 1 =>
      decide (r ≠ k % 6298) && scan (k + 1) ((2 * r) % 6298) len

private theorem advance_add (r m n : ℕ) :
    advance r (m + n) = advance (advance r m) n := by
  induction m generalizing r with
  | zero => simp [advance]
  | succ m ih => simpa [advance, Nat.succ_add] using ih ((2 * r) % 6298)

private theorem scan_add (k r m n : ℕ) :
    scan k r (m + n) =
      (scan k r m && scan (k + m) (advance r m) n) := by
  induction m generalizing k r with
  | zero => simp [scan, advance]
  | succ m ih =>
      simp only [Nat.succ_add, scan]
      rw [ih]
      simp [advance, Bool.and_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem scan_sound : ∀ {len k r : ℕ},
    scan k r len = true →
    r = 2 ^ k % 6298 →
    ∀ i, k ≤ i → i < k + len → ¬6298 ∣ 2 ^ i - i := by
  intro len
  induction len with
  | zero =>
      intro k r _ _ i _ hi
      omega
  | succ len ih =>
      intro k r hscan hr i hki hi hdiv
      rw [scan, Bool.and_eq_true, decide_eq_true_eq] at hscan
      by_cases hik : i = k
      · subst i
        apply hscan.1
        rw [hr]
        have hmod : k ≡ 2 ^ k [MOD 6298] :=
          (Nat.modEq_iff_dvd' k.lt_two_pow_self.le).2 hdiv
        exact hmod.symm
      · apply ih hscan.2 ?_ i (by omega) (by omega) hdiv
        simp only [hr, Nat.pow_succ]
        simp only [Nat.mul_mod, Nat.mod_mod,
          Nat.mod_eq_of_lt (by decide : 2 < 6298)]
        rw [Nat.mul_comm]
