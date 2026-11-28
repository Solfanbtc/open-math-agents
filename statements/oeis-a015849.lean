import Mathlib

/-!
# A015849: infinitely many n with 3 ∤ n and phi(n + 9) ∣ sigma(n)

Source: https://oeis.org/A015849
Credit: @Solfanbtc

A015849: the numbers `n` not congruent to 0 mod 3 such that `phi(n + 9)` divides `sigma(n)`.
Data 5, 7, 10, 31, 47, 79, 127, 145, …

The entry (R. Israel, Jan 10 2019): "Includes primes p such that (p+9)/8 is prime. Thus Dickson's
conjecture implies the sequence is infinite." (If `p + 9 = 8q` with `q` an odd prime, then
`phi(8q) = 4(q - 1) = (p + 1)/2` divides `sigma(p) = p + 1`.) `main` states the implied
conjecture: the sequence is infinite.

Conventions. `n` ranges over positive integers (offset 1); `sigma(n) = Sum_{d | n} d`
(`ArithmeticFunction.sigma 1`) and `phi` is `Nat.totient`. Checked with python3: the definition
reproduces the listed terms.
-/

namespace OMA.S_oeis_a015849

open ArithmeticFunction

/-- `n` is a term of A015849. -/
def InSeq (n : ℕ) : Prop := 0 < n ∧ ¬ 3 ∣ n ∧ (n + 9).totient ∣ sigma 1 n

/-- The conjecture implied by Dickson's conjecture: A015849 is infinite. -/
theorem main : {n : ℕ | InSeq n}.Infinite := by
  sorry

end OMA.S_oeis_a015849
