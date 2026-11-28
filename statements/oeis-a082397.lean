import Mathlib

/-!
# A082397: Number of directed aggregates of height <= 2 with n cells.

Source: https://oeis.org/A082397 (see A342912)
Credit: @Solfanbtc

A082397 (offset 1): 1, 2, 5, 11, 26, 62, 153, 385, 988, ... The entry gives no combinatorial
definition of "directed aggregates" beyond its name; we use the entry's explicit formula
(Vladeta Jovovic, stated as a formula, not as a conjecture):
`a(n) = ∑_{k=1..n} (-1)^(k+1) binomial(n+1, k+1) binomial(k, floor((k-1)/2))`.

A342912 (offset 0): `A342912(n) = [x^n] (1 - 2x - sqrt((1 - 3x)/(1 + x)))/(2x^3)`:
1, 1, 3, 6, 15, 36, ... Here `sqrt((1-3x)/(1+x))` is the power series `f` with constant term 1
and `f^2 (1 + x) = 1 - 3x` (unique); `1 - 2x - f` starts at `x^3`, so
`A342912(n) = [x^(n+3)] (1 - 2x - f)/2`. We state the claims for every such `f`.

Conjectures recorded in the entry (stated as a conjunction):
1. (Sean A. Irvine, Jul 16 2022) A082397 is the sequence of partial sums of A342912:
   `a(n) = ∑_{j=0}^{n-1} A342912(j)` for `n ≥ 1` (the offsets match: `a(1) = 1 = A342912(0)`);
2. (R. J. Mathar, Jun 27 2022) `(n+2) a(n) + (-3n-2) a(n-1) - n a(n-2) + 3n a(n-3) = 0`, stated for
   `n ≥ 4` (so that `a(n-3)` is a term, offset 1).

Sanity check (python, exact rationals): Jovovic's formula gives all 22 listed terms, the series
gives all 23 listed terms of A342912, and both claims hold for all `n ≤ 296`.
-/

namespace OMA.S_oeis_a082397

open PowerSeries

/-- A082397 via Jovovic's formula. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℤ) *
    (k.choose ((k - 1) / 2) : ℤ)

/-- The two conjectures, for the power series `f = sqrt((1-3x)/(1+x))`. -/
theorem main : ∀ f : PowerSeries ℚ, constantCoeff f = 1 → f ^ 2 * (1 + X) = 1 - 3 * X →
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = ∑ j ∈ Finset.range n, coeff (j + 3) (1 - 2 * X - f) / 2) ∧
    (∀ n : ℕ, 4 ≤ n →
      let m : ℤ := n;
      (m + 2) * a n + (-3 * m - 2) * a (n - 1) - m * a (n - 2) + 3 * m * a (n - 3) = 0) := by
  sorry

end OMA.S_oeis_a082397
