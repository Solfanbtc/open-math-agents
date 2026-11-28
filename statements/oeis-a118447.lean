import Mathlib

/-!
# A118447: Number of rooted n-edge one-vertex maps on the Klein bottle (dually: one-face maps).

Source: https://oeis.org/A118447
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 22 2016, %F line of A118447):
`-(n-2)(n-1)^2 a(n) + 2n(4n-5)(n-2) a(n-1) - 8n(n-1)(2n-3) a(n-2) = 0`.

Definition of `a`. By the entry's generating function (%F, used by its Mathematica program),
`Sum_n a(n) x^n = (R-1)^2 (R+1) (R+3) / (8 R^5)` with `R = sqrt(1 - 4x)`; the series starts at
`x^2` (offset 2: `a(2) = 4, a(3) = 42, ...`).

Formalization.
* Formal power series over `ℚ`. `R = 1 - 2 x c(x)`, with `c(x) = Sum Catalan(n) x^n`, is the
  square root of `1 - 4x` with constant term 1 (`R^2 = 1 - 4x` is the Catalan identity
  `c = 1 + x c^2`); it is invertible, and `a n` is the `x^n` coefficient of
  `(R-1)^2 (R+1) (R+3) R⁻⁵ / 8`.
* The recurrence involves `a(n-2)`, so with offset 2 it is stated for `n ≥ 4`, in `ℚ`. (It also
  holds at `n = 2, 3` with the coefficients `a(0) = a(1) = 0`.)

Checked with python3 (exact rational series): the generating function reproduces all listed
%S/%T/%U terms, and the recurrence holds for `2 ≤ n < 60`.
-/

namespace OMA.S_oeis_a118447

open PowerSeries

/-- The Catalan generating function over `ℚ`. -/
noncomputable def catalanGF : PowerSeries ℚ := PowerSeries.mk fun n => (catalan n : ℚ)

/-- `R = sqrt(1 - 4x) = 1 - 2 x c(x)`. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X * catalanGF

/-- The generating function `(R-1)^2 (R+1) (R+3) / (8 R^5)`. -/
noncomputable def gf : PowerSeries ℚ := (R - 1) ^ 2 * (R + 1) * (R + 3) * (R ^ 5)⁻¹ * C (1 / 8 : ℚ)

/-- A118447 (`a 0 = a 1 = 0`, `a 2 = 4`, ...). -/
noncomputable def a (n : ℕ) : ℚ := coeff n gf

/-- Mathar's conjectured recurrence for A118447. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℚ) - 2) * ((n : ℚ) - 1) ^ 2 * a n + 2 * n * (4 * n - 5) * ((n : ℚ) - 2) * a (n - 1)
      - 8 * n * ((n : ℚ) - 1) * (2 * n - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a118447
