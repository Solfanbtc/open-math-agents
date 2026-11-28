import Mathlib

/-!
# A000159: the t^3 coefficient of the ménage hit polynomials; recurrence and divisibility

Source: https://oeis.org/A000159
Credit: @Solfanbtc

A000159 (offset 3): `a(n) = A058087(n, n-3)`, where row `n` of A058087 lists the coefficients of
the ménage hit polynomial `U_n(t)` by descending powers, so `a(n)` is the coefficient of `t^3`
in `U_n(t) = Sum_{k=0..n} (2n/(2n-k)) * binomial(2n-k, k) * (n-k)! * (t-1)^k`
(Kaplansky and Riordan, as given in A058087). Data 2, 8, 20, 152, 994, 7888, …

The entry has two conjectures, both stated in `main`:
* (R. J. Mathar, 2015) `2(-252307n + 1041077) a(n) + (504614n^2 - 3362985n + 5118150) a(n-1)
  + (1280831n^2 - 7397886n + 6461565) a(n-2) + (746598n^2 - 2913543n - 1336090) a(n-3)
  + (-405481n^2 + 6175011n - 15469320) a(n-4) + (-375862n^2 + 4098537n - 8846430) a(n-5)
  + 2(-187931n + 560630) a(n-6) = 0`, read for `n ≥ 9`, so that every index is at least the
  offset 3.
* (M. van Hoeij, 2019) `a(n) + 2a(n+p) + a(n+2p)` is divisible by `p` for every prime `p ≠ 3`,
  read for all `n ≥ 3`.

Checked with python3 (exact rationals): the formula reproduces the first 12 terms; the
recurrence holds for `9 ≤ n < 135`; the divisibility holds for all primes `p < 45`, `p ≠ 3`, and
`3 ≤ n < 140 - 2p` (and fails for `p = 3`, e.g. at `n = 4`, as the exception says).
-/

namespace OMA.S_oeis_a000159

open Polynomial

/-- The ménage hit polynomial `U_n(t)` (Kaplansky-Riordan), over `ℚ`. -/
noncomputable def U (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((2 * n : ℚ) / (2 * n - k) * (2 * n - k).choose k * (n - k).factorial) * (X - 1) ^ k

/-- A000159: `a(n) = A058087(n, n-3)`, the coefficient of `t^3` in `U_n(t)`. -/
noncomputable def a (n : ℕ) : ℚ := (U n).coeff 3

/-- Mathar's recurrence and van Hoeij's divisibility conjecture for A000159. -/
theorem main :
    (∀ n : ℕ, 9 ≤ n →
      2 * (-252307 * (n : ℚ) + 1041077) * a n
        + (504614 * (n : ℚ) ^ 2 - 3362985 * n + 5118150) * a (n - 1)
        + (1280831 * (n : ℚ) ^ 2 - 7397886 * n + 6461565) * a (n - 2)
        + (746598 * (n : ℚ) ^ 2 - 2913543 * n - 1336090) * a (n - 3)
        + (-405481 * (n : ℚ) ^ 2 + 6175011 * n - 15469320) * a (n - 4)
        + (-375862 * (n : ℚ) ^ 2 + 4098537 * n - 8846430) * a (n - 5)
        + 2 * (-187931 * (n : ℚ) + 560630) * a (n - 6) = 0) ∧
    (∀ p n : ℕ, p.Prime → p ≠ 3 → 3 ≤ n →
      ∃ m : ℤ, a n + 2 * a (n + p) + a (n + 2 * p) = p * m) := by
  sorry

end OMA.S_oeis_a000159
