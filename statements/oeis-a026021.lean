import Mathlib

/-!
# A026021: a(n) = T(n, [n/2]), where T is the array defined in A026009.

Source: https://oeis.org/A026021
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A026021, formula section, Jun 20 2013), as printed:
-(n+7)*(5*n-34)*a(n) + 8*(-n-14)*a(n-1) + (27*n^2-83*n-428)*a(n-2) + 8*(4*n+5)*a(n-3)
44*(n-3)*(7*n-27)*a(n-4) = 0.

Minimal fix: the printed formula has no operator before the last term ("... a(n-3) 44*..."),
so it is not a well-formed equation; reading it as "+ 44*" or "- 44*" fails already at n = 4
(checked in Python). Fitting the unique recurrence of order 4 with coefficients of degree ≤ 2
to the data (Python, exact arithmetic, n = 4..59) gives exactly Mathar's first four
coefficients and the last coefficient -4*(n-3)*(7*n-27): the printed "44*" is a garbled "-4*"
(the minus sign lost / turned into a 4). The statement below uses
... + 8*(4*n+5)*a(n-3) - 4*(n-3)*(7*n-27)*a(n-4) = 0, checked in Python for 4 ≤ n < 300.

Conventions:
* A026009 is the triangle T(n,0) = 1 for n ≥ 0; T(1,1) = 1; for n ≥ 2,
  T(n,k) = T(n-1,k-1) + T(n-1,k) for k = 1..[(n+1)/2], and T(n, n/2+1) = T(n-1, n/2) if n is
  even; entries outside the rows are 0. This reproduces the example rows of A026009.
* a(n) = T(n, [n/2]) (offset 0). Checked in Python: all 37 listed terms.
* The recurrence involves a(n-4), so it is stated for n ≥ 4; it is evaluated in ℤ.
-/

namespace OMA.S_oeis_a026021

/-- The triangle A026009 (0 outside the rows). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if k = 0 then 1
    else if k ≤ (n + 3) / 2 then T (n + 1) (k - 1) + T (n + 1) k
    else if n % 2 = 0 ∧ k = (n + 2) / 2 + 1 then T (n + 1) ((n + 2) / 2)
    else 0

/-- A026021: `a(n) = T(n, [n/2])`. -/
def a (n : ℕ) : ℤ := T n (n / 2)

/-- Mathar's conjectured recurrence for A026021 (with the last operator restored as `- 4*`). -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℤ) + 7) * (5 * (n : ℤ) - 34) * a n + 8 * (-(n : ℤ) - 14) * a (n - 1)
      + (27 * (n : ℤ) ^ 2 - 83 * n - 428) * a (n - 2) + 8 * (4 * (n : ℤ) + 5) * a (n - 3)
      - 4 * ((n : ℤ) - 3) * (7 * (n : ℤ) - 27) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026021
