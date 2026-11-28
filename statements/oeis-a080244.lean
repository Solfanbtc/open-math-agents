import Mathlib

/-!
# A080244: Signed generalized Fibonacci numbers.

Source: https://oeis.org/A080244
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Nov 24 2012, OEIS A080244):
  (n+1) a(n) + (7n-2) a(n-1) + 4(2n-1) a(n-2) + 6(n-1) a(n-3) + (-5n+1) a(n-4) + (-n+2) a(n-5) = 0.

Index convention (minimal fix). The entry has offset 1 (a(1) = 1, a(2) = -2, a(3) = 7, ...); with
that indexing the recurrence fails (for every n >= 6 checked). It holds when the terms are indexed
from 0, b(m) = a(m+1) (b(0) = 1, b(1) = -2, ...), for all m >= 5 (checked for m < 55). `main`
states the recurrence for b.

Definition. The sequence is taken from its generating function (C. Ronaldo, in the entry):
  Σ_{n>=1} a(n) x^n = (-1 - x + 2x^2 + sqrt(1 + 6x + x^2)) / (2 (1 + x + x^2 - x^3)),
as formal power series over ℚ, where sqrt(1 + 6x + x^2) is the power series S with S^2 = 1 + 6x + x^2
and constant term 1 (unique). `main` quantifies over S and the g.f. A satisfying these equations,
and b(m) is the coefficient of x^(m+1) in A. Checked numerically: the coefficients are 1, -2, 7, -26,
107, ..., matching the listed terms.
-/

namespace OMA.S_oeis_a080244

open PowerSeries

theorem main : ∀ S A : PowerSeries ℚ, S ^ 2 = 1 + 6 * X + X ^ 2 → constantCoeff S = 1 →
    A * (2 * (1 + X + X ^ 2 - X ^ 3)) = -1 - X + 2 * X ^ 2 + S →
    ∀ m : ℕ, 5 ≤ m →
      ((m : ℚ) + 1) * coeff (m + 1) A + (7 * (m : ℚ) - 2) * coeff m A
        + 4 * (2 * (m : ℚ) - 1) * coeff (m - 1) A + 6 * ((m : ℚ) - 1) * coeff (m - 2) A
        + (-5 * (m : ℚ) + 1) * coeff (m - 3) A + (-(m : ℚ) + 2) * coeff (m - 4) A = 0 := by
  sorry

end OMA.S_oeis_a080244
