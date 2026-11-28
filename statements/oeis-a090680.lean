import Mathlib

/-!
# A090680: Number of primes p such that n < p < n+A033677(n).

Source: https://oeis.org/A090680
Credit: @Solfanbtc

Conjecture (OEIS A090680): no a(n) is zero, i.e. for every n >= 2 (offset 2) there is a prime p
with n < p < n + A033677(n).

A033677(n) is the smallest divisor d of n with d >= sqrt(n), i.e. with n <= d^2. (For n = 1 the
interval (1, 2) is empty, consistent with the offset 2.) For prime n this is Bertrand's postulate;
for n = m^2 it is a prime in (m^2, m^2 + m), half of Oppermann's conjecture.
Checked numerically for 2 <= n < 10^6.
-/

namespace OMA.S_oeis_a090680

/-- `d` is A033677(n): the least divisor of `n` that is at least `sqrt n`. -/
def IsA033677 (n d : ℕ) : Prop := IsLeast {k : ℕ | k ∣ n ∧ n ≤ k ^ 2} d

theorem main : ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ, IsA033677 n d →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < n + d := by
  sorry

end OMA.S_oeis_a090680
