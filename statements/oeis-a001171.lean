import Mathlib

/-!
# A001171: From least significant term in expansion of E( tr (X'*X)^n ), X rectangular and Gaussian. Also number of types of sequential n-swap moves for traveling salesman problem.

Source: https://oeis.org/A001171
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Aug 07 2013, in the entry), for n >= 5:
(n+1)*a(n) = -(4*n-1)*a(n-1) + (5*n^3 - 16*n^2 + 13*n - 1)*a(n-2)
  + (10*n^3 - 68*n^2 + 150*n - 107)*a(n-3) - (n-4)*(n-2)^2*(2*n-7)^2*a(n-4).

Conventions.
* a(n) (n ≥ 1) is given by the closed formula of Hanlon, Stanley & Stembridge (end of Sect. 5
  of their paper), in the corrected form quoted in the entry (Herman Jamke, Aug 01 2010; this is
  the entry's Maple/Mathematica program):
    a(k) = 2^(3k-2) k! (k-1)!^2 / (2k)!
         + ∑_{a=1}^{k-1} ∑_{b=1}^{min(a,k-a)} c(a,b,k) ·
             (2^(a-b-1) (2b)! (a-1)! (k-a-b+1)! / ((2b-1) b!))^2,
    c(a,b,k) = (-1)^k (-2)^(a-b+1) k (2a-2b+1) (a-1)! /
         ((k+a-b+1)(k+a-b)(k-a+b)(k-a+b-1) (k-a-b)! (2a-1)! (b-1)!).
  It is computed in ℚ (the exponent a-b-1 can be -1; all denominators are nonzero in the
  summation range). Defining the sequence through this proved formula instead of through the
  Gaussian-matrix moments or n-swap types keeps the values unchanged: checked with python3 that
  it reproduces all 19 listed terms.
* The recurrence is stated in ℚ for every n ≥ 5 (it involves a(n-4), so a(1), ... are used).
  Checked with python3 for 5 ≤ n ≤ 80.
-/

namespace OMA.S_oeis_a001171

/-- The coefficient `c(a, b, k)` of Hanlon's formula. -/
def coef (a b k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k * (-2 : ℚ) ^ (a - b + 1) * k * (2 * a - 2 * b + 1 : ℕ) * (a - 1).factorial) /
    (((k + a - b + 1 : ℕ) : ℚ) * (k + a - b : ℕ) * (k - a + b : ℕ) * (k - a + b - 1 : ℕ) *
      (k - a - b).factorial * (2 * a - 1).factorial * (b - 1).factorial)

/-- A001171(k) for `k ≥ 1`, by Hanlon's formula (corrected form quoted in the entry). -/
def A (k : ℕ) : ℚ :=
  (2 : ℚ) ^ (3 * k - 2) * k.factorial * (k - 1).factorial ^ 2 / (2 * k).factorial +
    ∑ a ∈ Finset.Icc 1 (k - 1), ∑ b ∈ Finset.Icc 1 (min a (k - a)),
      coef a b k *
        ((2 : ℚ) ^ ((a : ℤ) - b - 1) * (2 * b).factorial * (a - 1).factorial *
            (k - a - b + 1).factorial / ((2 * b - 1 : ℕ) * b.factorial)) ^ 2

theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 1) * A n =
      -(4 * (n : ℚ) - 1) * A (n - 1) +
        (5 * (n : ℚ) ^ 3 - 16 * n ^ 2 + 13 * n - 1) * A (n - 2) +
        (10 * (n : ℚ) ^ 3 - 68 * n ^ 2 + 150 * n - 107) * A (n - 3) -
        ((n : ℚ) - 4) * ((n : ℚ) - 2) ^ 2 * (2 * (n : ℚ) - 7) ^ 2 * A (n - 4) := by
  sorry

end OMA.S_oeis_a001171
