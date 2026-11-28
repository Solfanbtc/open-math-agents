import Mathlib

/-!
# A075125: Number of parallelogram polyominoes of site-perimeter n (also called staircase polyominoes, although that term is overused).

Source: https://oeis.org/A075125
Credit: @Solfanbtc

Definition used: the generating function of the entry (FORMULA; Maple/Mathematica programs, from
Delest–Gouyou-Beauchamps–Vauquelin and Bousquet-Mélou–Rechnitzer):
Sum_{n ≥ 1} a(n) z^n = 4 z^4 / (1 + z - z^2 + sqrt((1 + z + z^2)(1 - 3 z + z^2)))^2.
Here sqrt is the formal power series square root with constant term 1: the unique `u ∈ ℚ[[z]]`
with `u^2 = (1 + z + z^2)(1 - 3 z + z^2)` and constant coefficient 1. The theorem quantifies over
every such `u` (there is exactly one). `1 + z - z^2 + u` has constant term 2, so it is invertible.
This reproduces the data 0, 0, 0, 1, 0, 2, 2, 5, 10, 21, 46, ... (offset 1; checked).

Conjecture (R. J. Mathar, May 30 2016):
-(2n-11)(n-2)(2n-9) a(n) + 4(2n-11)(n-3)(n-5) a(n-1) + (4n^3-60n^2+317n-582) a(n-2)
  + 2(2n-7)(2n^2-26n+81) a(n-3) - (n-10)(2n-7)(2n-9) a(n-4) = 0.
It involves a(n-4) and the offset is 1, so it is stated for n ≥ 5. Checked for 5 ≤ n < 60.
-/

namespace OMA.S_oeis_a075125

open PowerSeries

/-- The radicand `(1 + z + z^2)(1 - 3z + z^2)`. -/
noncomputable def radicand : PowerSeries ℚ := (1 + X + X ^ 2) * (1 - 3 * X + X ^ 2)

/-- The coefficients of `4 z^4 / (1 + z - z^2 + u)^2`, where `u` is the square root of the
radicand; `a u n` is A075125(n) for `n ≥ 1`. -/
noncomputable def a (u : PowerSeries ℚ) (n : ℕ) : ℚ :=
  coeff n (4 * X ^ 4 * ((1 + X - X ^ 2 + u)⁻¹) ^ 2)

theorem main : ∀ u : PowerSeries ℚ, u ^ 2 = radicand → constantCoeff u = 1 →
    ∀ n : ℕ, 5 ≤ n →
      -(2 * (n : ℚ) - 11) * (n - 2) * (2 * n - 9) * a u n
        + 4 * (2 * (n : ℚ) - 11) * (n - 3) * (n - 5) * a u (n - 1)
        + (4 * (n : ℚ) ^ 3 - 60 * n ^ 2 + 317 * n - 582) * a u (n - 2)
        + 2 * (2 * (n : ℚ) - 7) * (2 * n ^ 2 - 26 * n + 81) * a u (n - 3)
        - ((n : ℚ) - 10) * (2 * n - 7) * (2 * n - 9) * a u (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a075125
