import Mathlib

/-!
# A055231: Powerfree part of n: product of primes that divide n only once.

Source: https://oeis.org/A055231
Credit: @Solfanbtc

`a(n) = ∏ p` over the primes `p` with `p ∣ n` and `p^2 ∤ n` (the primes occurring exactly once in
the prime factorization of `n`); `a(1) = 1`. Data: 1, 2, 3, 1, 5, 6, 7, 1, 1, 10, ...

Conjecture (Velin Yanev, Feb 06 2019): for all `n, m > 0`,
`a(n m) = a(n) a(m) / (gcd(n, a(m)) gcd(m, a(n)))`.
N. J. A. Sloane notes that this follows easily from a comment of Vladeta Jovovic; we state it
faithfully nevertheless. The division is exact; we state it with natural-number division.

Sanity check: python gives all 80 listed terms and confirms the identity (with exact division)
for all `1 ≤ n, m ≤ 300`; `#eval` of `a` in Lean gives the listed terms and the identity (in
multiplied-out form) for `1 ≤ n, m ≤ 60`.
-/

namespace OMA.S_oeis_a055231

/-- The powerfree part of `n`: the product of the primes occurring exactly once in `n`. -/
def a (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.primeFactorsList.count p = 1), p

/-- Yanev's identity for the powerfree part. -/
theorem main : ∀ n m : ℕ, 0 < n → 0 < m →
    a (n * m) = a n * a m / (Nat.gcd n (a m) * Nat.gcd m (a n)) := by
  sorry

end OMA.S_oeis_a055231
