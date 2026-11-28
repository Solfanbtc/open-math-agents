import Mathlib

/-!
# A067803: Numbers n such that sigma(n)-sigma(n+1)=n.

Source: https://oeis.org/A067803
Credit: @Solfanbtc

Conjecture (OEIS A067803, comment): the sequence gives even values only, i.e. every positive
integer n with σ(n) - σ(n+1) = n is even.

Conventions:
* σ is the sum of divisors (`ArithmeticFunction.sigma 1`); the equation is taken in ℤ. n ranges
  over the positive integers (offset 1).
* Checked in Python: the solutions n ≤ 10^7 are 532, 954, 104944, 918080, as in %S, all even.
  Per the entry (Resta), all terms below 10^13 are the 8 listed, all even.
-/

namespace OMA.S_oeis_a067803

open ArithmeticFunction

/-- Every solution of `σ(n) - σ(n+1) = n` is even. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (sigma 1 n : ℤ) - (sigma 1 (n + 1) : ℤ) = n → Even n := by
  sorry

end OMA.S_oeis_a067803
