import Mathlib

/-!
# A005561: Number of walks on square lattice. Column y=3 of A052174.

Source: https://oeis.org/A005561
Credit: @Solfanbtc

Conjecture (R. J. Mathar, OEIS A005561, formula section, Apr 02 2017):
(n-2)*(n-3)*(2*n+1)*(n+6)*(n+5)*a(n) - 4*n*(n+1)*(2*n^2+4*n+33)*a(n-1)
  - 16*n^2*(n-1)*(2*n+3)*(n+1)*a(n-2) = 0.

Conventions:
* The offset of A005561 is 3: a(3) = 1, a(4) = 4, a(5) = 24, a(6) = 84, ... Mathar's Maple
  program, from which the conjecture comes, uses this offset (seq(A005561(n), n=3..30)), and
  the recurrence is false with offset 0 (it fails already at n = 2).
* The terms are given by the closed formula of Paul D. Hanna (formula section; it is also the
  entry's PARI and Magma program, with offset 0): with m = n - 3,
  a(n) = C(m+4, ceil(m/2)) C(m+3, floor(m/2)) - C(m+4, ceil((m-1)/2)) C(m+3, floor((m-1)/2)),
  where for m = 0 the second product is 0 (floor(-1/2) = -1). For m ≥ 1,
  ceil(m/2) = (m+1)/2, floor(m/2) = m/2, ceil((m-1)/2) = m/2 and floor((m-1)/2) = (m-1)/2
  with natural-number division. Checked in Python: this gives all 26 listed terms of
  %S/%T/%U.
* The recurrence involves a(n-2), so it is stated for n ≥ 5 (both a(n-1) and a(n-2) within the
  offset). Checked in Python for 5 ≤ n < 200.
-/

namespace OMA.S_oeis_a005561

/-- A005561 (offset 3), by Hanna's closed formula; `a n` is meant for `n ≥ 3`. -/
def a (n : ℕ) : ℤ :=
  let m := n - 3
  (Nat.choose (m + 4) ((m + 1) / 2) * Nat.choose (m + 3) (m / 2) : ℤ) -
    (if m = 0 then 0 else (Nat.choose (m + 4) (m / 2) * Nat.choose (m + 3) ((m - 1) / 2) : ℤ))

/-- Mathar's conjectured holonomic recurrence for A005561. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) - 2) * ((n : ℤ) - 3) * (2 * n + 1) * (n + 6) * (n + 5) * a n
      - 4 * n * (n + 1) * (2 * n ^ 2 + 4 * n + 33) * a (n - 1)
      - 16 * n ^ 2 * ((n : ℤ) - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005561
