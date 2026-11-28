import Mathlib

/-!
# A067299: Second column of triangle A067298.

Source: https://oeis.org/A067299
Credit: @Solfanbtc

a(n) = A067298(n+1, 1), where A067298(n, m) = Sum_{i=0..m} C(2,2; i)*C(2,2; n-i) and
C(2,2; n) = A064340(n). Hence a(n) = C(2,2; 0)*C(2,2; n+1) + C(2,2; 1)*C(2,2; n)
= C(2,2; n+1) + C(2,2; n), since C(2,2; 0) = C(2,2; 1) = 1.
C(2,2; n) is given by the explicit formula of A064340:
a(0) = a(1) = 1 and, for n ≥ 2,
C(2,2; n) = (4^(n-1)/(n-1)) * Sum_{m=0..n-2} (m+1)*(m+2)*binomial(2*(n-2)-m, n-2-m)/2^(m+1).
This reproduces the data 2, 5, 32, 284, 2960, 33872, ... (checked).

Conjecture (R. J. Mathar, Jul 21 2016):
n*(17*n-7)*a(n) + 2*(-119*n^2+270*n-96)*a(n-1) - 16*(17*n+10)*(2*n-3)*a(n-2) = 0.
It involves a(n-2), so it is stated for n ≥ 2 (offset 0). Checked for 2 ≤ n < 300.
-/

namespace OMA.S_oeis_a067299

/-- The generalized Catalan numbers C(2,2; n) = A064340(n), by the explicit formula. -/
def C22 (n : ℕ) : ℚ :=
  if n < 2 then 1 else
    (4 : ℚ) ^ (n - 1) / (n - 1 : ℕ) * ∑ m ∈ Finset.range (n - 1),
      ((m + 1) * (m + 2) * ((2 * (n - 2) - m).choose (n - 2 - m) : ℕ) : ℚ) / 2 ^ (m + 1)

/-- A067299. -/
def a (n : ℕ) : ℚ := C22 (n + 1) + C22 n

theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * (17 * n - 7) * a n + 2 * (-119 * (n : ℚ) ^ 2 + 270 * n - 96) * a (n - 1)
      - 16 * (17 * (n : ℚ) + 10) * (2 * n - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a067299
