import Mathlib

/-!
# A063956: Sum of the unitary prime divisors of n.

Source: https://oeis.org/A063956
Credit: @Solfanbtc

Conjecture (OEIS A063956, %F line): a(n m) = a(n) + a(m) - a(gcd(n^2, m)) - a(gcd(n, m^2)) for all
n and m > 0.

a(n) is the sum of the primes p dividing n exactly once (p ∣ n, p^2 ∤ n), i.e. the primes p with
p-adic valuation 1 (a(1) = 0). The identity is stated in ℤ.
Checked numerically for 1 <= n, m < 150.
-/

namespace OMA.S_oeis_a063956

/-- Sum of the unitary prime divisors of `n`. -/
def a (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

theorem main : ∀ n m : ℕ, 0 < n → 0 < m →
    (a (n * m) : ℤ) = a n + a m - a (Nat.gcd (n ^ 2) m) - a (Nat.gcd n (m ^ 2)) := by
  sorry

end OMA.S_oeis_a063956
