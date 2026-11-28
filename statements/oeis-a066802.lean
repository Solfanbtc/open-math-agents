import Mathlib

/-!
# A066802: a(n) = binomial(6*n,3*n).

Source: https://oeis.org/A066802
Credit: @Solfanbtc

Conjecture (OEIS A066802): a(n) = [x^n] G(x)^(2n), where
G(x) = (1 + x)(1 - 6x + x^2)/(2x) + (x^2 - 1) sqrt(1 - 14x + x^2)/(2x) = 1 + 10x + 81x^2 + 720x^3 + ...,
and G satisfies x G(x)^2 - (1 - 5x - 5x^2 + x^3) G(x) + (1 + x)^4 = 0.

Translation: G is taken as a formal power series over ℚ characterized by the quadratic equation
of the entry. This equation determines G uniquely: comparing coefficients of x^n gives
G_n = [x^(n-1)] G^2 + 5 G_{n-1} + 5 G_{n-2} - G_{n-3} + binomial(4, n), with G_0 = 1, which is the
branch 1 + 10x + 81x^2 + ... of the closed form. `main` quantifies over the power series satisfying
the equation (there is exactly one). Checked numerically: the recursion gives 1, 10, 81, 720, 7056,
... and [x^n] G^(2n) = binomial(6n, 3n) for n < 20.
-/

namespace OMA.S_oeis_a066802

open PowerSeries

theorem main : ∀ G : PowerSeries ℚ,
    X * G ^ 2 - (1 - 5 * X - 5 * X ^ 2 + X ^ 3) * G + (1 + X) ^ 4 = 0 →
    ∀ n : ℕ, coeff n (G ^ (2 * n)) = ((6 * n).choose (3 * n) : ℚ) := by
  sorry

end OMA.S_oeis_a066802
