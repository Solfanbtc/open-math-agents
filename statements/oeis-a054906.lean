import Mathlib

/-!
# A054906: Smallest number x such that sigma(x+2n) = sigma(x)+2n (first definition).

Source: https://oeis.org/A054906
Credit: @Solfanbtc

The entry gives three definitions of a(n), n ≥ 1:
1. the smallest number x with sigma(x+2n) = sigma(x) + 2n;
2. the smallest number x with phi(x+2n) = phi(x) + 2n;
3. the smallest prime p such that p + 2n is prime (A020483);
and states "The 3 definitions are identical or conjectured to be identical" (N. J. A. Sloane,
2017: "If it can be proved that all these definitions are identical, then this entry should be
merged with A020483"). Stated: for every n ≥ 1 the three minima exist and coincide.

Conventions.
* "Number" means positive integer (x ≥ 1); σ = `ArithmeticFunction.sigma 1`, φ = `Nat.totient`.
* The sequence is listed for every n ≥ 1, so existence of the three minima is part of the claim
  (for definition 3 it is the existence of two primes with difference 2n).
* python3 (exact, x < 4·10^5): the three minima agree for 1 ≤ n < 300.
-/

namespace OMA.S_oeis_a054906

open ArithmeticFunction

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ,
      IsLeast {x : ℕ | 1 ≤ x ∧ sigma 1 (x + 2 * n) = sigma 1 x + 2 * n} p ∧
      IsLeast {x : ℕ | 1 ≤ x ∧ Nat.totient (x + 2 * n) = Nat.totient x + 2 * n} p ∧
      IsLeast {x : ℕ | x.Prime ∧ (x + 2 * n).Prime} p := by
  sorry

end OMA.S_oeis_a054906
