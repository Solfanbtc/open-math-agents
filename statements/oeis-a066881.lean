import Mathlib

/-!
# A066881: Numbers k such that sigma(phi(k))/sigma(k) is an integer >= 4.

Source: https://oeis.org/A066881
Credit: @Solfanbtc

Conjecture (OEIS A066881, comment): all natural numbers 1, 2, 3, ..., n will eventually occur
among the integer values of sigma(phi(k))/sigma(k), i.e. every positive integer m equals
σ(φ(k))/σ(k) for some k ≥ 1.

Conventions:
* σ is the sum of divisors (`ArithmeticFunction.sigma 1`), φ is `Nat.totient`; "σ(φ(k))/σ(k) is
  the integer m" is written without division as σ(φ(k)) = m · σ(k) (σ(k) > 0 for k ≥ 1).
* Checked in Python for k ≤ 4·10^6: the integer values taken are exactly 1, 2, 3, 4, and 4 is
  first taken at k = 121679 = a(1) (5 is not reached in that range).
-/

namespace OMA.S_oeis_a066881

open ArithmeticFunction

/-- Every positive integer is an integer value of `σ(φ(k))/σ(k)`. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, 1 ≤ k ∧ sigma 1 (Nat.totient k) = m * sigma 1 k := by
  sorry

end OMA.S_oeis_a066881
