import Mathlib

/-!
# A054979: e-perfect numbers.

Source: https://oeis.org/A054979
Credit: @Solfanbtc

e-perfect numbers: numbers k such that the sum of the e-divisors (exponential divisors) of k
equals 2k. Conjecture (Jon Perry, Nov 13 2012, in the entry): every e-perfect number is
divisible by 36.

Conventions.
* The e-divisors of x = ∏ p_i^(r_i) are the numbers ∏ p_i^(s_i) with s_i ∣ r_i for all i (entry
  comment); since r_i ≥ 1 forces s_i ≥ 1, they are the divisors d of x such that for every prime
  p the exponent of p in d divides the exponent of p in x (with Nat divisibility, 0 ∣ r only
  for r = 0, and every exponent divides 0). `Nat.factorization` gives the exponents.
* python3: the e-perfect numbers below 2·10^5 are 36, 180, 252, 396, 468, ... (1739 of them,
  matching the data), all divisible by 36.
-/

namespace OMA.S_oeis_a054979

/-- The exponential divisors of n. -/
def eDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => ∀ p ∈ n.primeFactors, d.factorization p ∣ n.factorization p

/-- Sum of the e-divisors (A051377). -/
def eSigma (n : ℕ) : ℕ := ∑ d ∈ eDivisors n, d

theorem main : ∀ n : ℕ, 1 ≤ n → eSigma n = 2 * n → 36 ∣ n := by
  sorry

end OMA.S_oeis_a054979
