import Mathlib

/-!
# A004982: a(n) = (2^n/n!) * Product_{k=0..n-1} (4*k + 3).

Source: https://oeis.org/A004982
Credit: @Solfanbtc

Conjecture (Peter Bala, OEIS A004982, comment, Dec 22 2019): a(p*n) = a(n) (mod p^2) for
prime p == 1 (mod 4) and all positive integers n.

Conventions:
* a(n) = 2^n * Product_{k=0..n-1} (4k+3) / n!, offset 0. The division is exact (a(n) =
  (-8)^n binomial(-3/4, n) is an integer); the natural-number quotient below is therefore
  a(n). Checked in Python: this gives all 23 listed terms of %S/%T/%U.
* The congruence is in ℤ. Checked in Python for all primes p ≡ 1 (mod 4) below 60 and
  1 ≤ n ≤ 11 (it fails for p ≡ 3 (mod 4), e.g. p = 3, n = 1, so the restriction matters).
-/

namespace OMA.S_oeis_a004982

/-- A004982: `(2^n / n!) * Π_{k<n} (4k+3)`. -/
def a (n : ℕ) : ℕ := 2 ^ n * (∏ k ∈ Finset.range n, (4 * k + 3)) / Nat.factorial n

/-- Bala's conjecture: `a(p n) ≡ a(n) (mod p^2)` for primes `p ≡ 1 (mod 4)` and `n ≥ 1`. -/
theorem main : ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ n : ℕ, 1 ≤ n →
    (a (p * n) : ℤ) ≡ (a n : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  sorry

end OMA.S_oeis_a004982
