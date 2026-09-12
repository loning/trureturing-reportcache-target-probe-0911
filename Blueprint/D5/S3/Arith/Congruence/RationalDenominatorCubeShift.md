# The Rational-Denominator Cube Shift

## Abstract

A residue-class gcd identity proves Cicuttin's denominator formula for OEIS A152020.

**Definition 1.1 (The A152020 denominator sequence).**

$$\forall n \in \mathbb{N}, \operatorname{a}\left(n\right) = \frac{\operatorname{den}\left(\frac{8}{9 \cdot n^{2}}\right)}{9}$$

*Formalization.* `D5/S3/Arith/Congruence/RationalDenominatorCubeShift.a` (`✓ std3`).

*Citation.* Andres Cicuttin (2017). *OEIS A152020, Denominator of 8/(9*n^2) divided by 9*. URL: <https://oeis.org/A152020>.

*Commentary.*

For every natural n, a(n) is the positive reduced denominator Rat.den of 8 divided by 9 times n squared, followed by natural-number division by 9. The denominator is always divisible by 9, so this final division is exact.

**Theorem 1.2 (Cicuttin's denominator formula).**

$$\forall n \in \mathbb{N}, 1 \le n \Rightarrow \operatorname{a}\left(n\right) = \operatorname{den}\left(\frac{(n - 2)^{3}}{n^{2}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/RationalDenominatorCubeShift.cicuttin_a152020` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a152020-rational-denominator-cube-shift` (proved) by `D5/S3/Arith/Congruence/RationalDenominatorCubeShift.cicuttin_a152020`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a152020-rational-denominator-cube-shift","declaration_gid":"D5/S3/Arith/Congruence/RationalDenominatorCubeShift.cicuttin_a152020","resolution_kind":"proved"} -->

*Citation.* Andres Cicuttin (2017). *OEIS A152020, Denominator of 8/(9*n^2) divided by 9*. URL: <https://oeis.org/A152020>.

*Commentary.*

For a positive index n, the numerator n minus 2 is formed in the integers, then cubed and divided by n squared in the rationals. Reduced-denominator formulas turn both sides into gcd quotients. Splitting n modulo 4 proves that gcd(n squared,(n-2) cubed) equals gcd(n squared,8): the common value is 1 for odd n, 4 when n is 2 modulo 4, and 8 when 4 divides n. The index n=1 is evaluated separately.

## References

- Truth anchor: `D5/S3/Arith/Congruence/RationalDenominatorCubeShift.a`
- Truth anchor: `D5/S3/Arith/Congruence/RationalDenominatorCubeShift.cicuttin_a152020`
