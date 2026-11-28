import Mathlib

/-!
# A000181: a(n) = A058087(n,n-4).

Source: https://oeis.org/A000181
Credit: @Solfanbtc

A058087 is the triangle of coefficients of the ménage hit polynomials, by descending powers:
row `n` lists the coefficients of (Kaplansky and Riordan)
`U_n(t) = ∑_{k=0..n} (2n/(2n-k)) * binomial(2n-k, k) * (n-k)! * (t-1)^k`,
higher powers first, so `A058087(n, n-4)` is the coefficient of `t^4` in `U_n(t)`.
A000181 has offset 4: 2, 15, 60, 469, 3660, 32958, ... (`a(4) = 2`).
For `n ≥ 1` and `k ≤ n` we have `2n - k ≥ n > 0`, so the division is harmless.

The entry records two conjectures, stated here as a conjunction:
1. (R. J. Mathar, Nov 02 2015) for every `n` such that `a(n), ..., a(n-4)` are all terms
   of the sequence (i.e. `n ≥ 8`):
   `3(2111n-8303)(n-4)(2n-9)^2 a(n) - (n-3)(25332n^4 - 377236n^3 + 1898681n^2 - 3320738n + 484000) a(n-1)
    - 2(n-4)(12140n^4 - 118152n^3 + 337063n^2 - 377436n + 225720) a(n-2)
    + (1052n^5 - 40656n^4 + 266063n^3 - 549153n^2 + 49850n + 655200) a(n-3)
    + (263n+640)(n-3)(2n-7)^2 a(n-4) = 0`;
2. (Mark van Hoeij, Jun 10 2019) `a(n) + 2a(n+p) + a(n+2p)` is divisible by `p` for every prime
   `p > 3` (and every index `n ≥ 4` of the sequence).
The values `a(n)` are integers; the divisibility is stated as `∃ m : ℤ, ... = p * m`.

Sanity check (python, exact rationals): the formula gives all 20 listed terms (integers), the
recurrence holds for `8 ≤ n < 200`, and the congruence for all primes `5 ≤ p < 60` and
`4 ≤ n < 200 - 2p`.
-/

namespace OMA.S_oeis_a000181

open Polynomial

/-- The ménage hit polynomial `U_n(t)` (Kaplansky–Riordan formula, as in A058087). -/
noncomputable def U (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((2 * n : ℚ) / (2 * n - k) * ((2 * n - k).choose k : ℚ) * ((n - k).factorial : ℚ)) *
      (X - 1) ^ k

/-- `a(n) = A058087(n, n-4)`, the coefficient of `t^4` in `U_n(t)` (meaningful for `n ≥ 4`). -/
noncomputable def a (n : ℕ) : ℚ := (U n).coeff 4

/-- Mathar's recurrence and van Hoeij's congruence for A000181. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n →
      let m : ℚ := n
      3 * (2111 * m - 8303) * (m - 4) * (2 * m - 9) ^ 2 * a n
        - (m - 3) * (25332 * m ^ 4 - 377236 * m ^ 3 + 1898681 * m ^ 2 - 3320738 * m + 484000)
          * a (n - 1)
        - 2 * (m - 4) * (12140 * m ^ 4 - 118152 * m ^ 3 + 337063 * m ^ 2 - 377436 * m + 225720)
          * a (n - 2)
        + (1052 * m ^ 5 - 40656 * m ^ 4 + 266063 * m ^ 3 - 549153 * m ^ 2 + 49850 * m + 655200)
          * a (n - 3)
        + (263 * m + 640) * (m - 3) * (2 * m - 7) ^ 2 * a (n - 4) = 0) ∧
    (∀ n p : ℕ, 4 ≤ n → p.Prime → 3 < p →
      ∃ k : ℤ, a n + 2 * a (n + p) + a (n + 2 * p) = (p : ℚ) * k) := by
  sorry

end OMA.S_oeis_a000181
