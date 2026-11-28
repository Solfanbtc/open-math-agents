import Mathlib

/-!
# A085331: Numbers k such that phi(rev(k)) = k.

Source: https://oeis.org/A085331
Credit: @Solfanbtc

`rev(k)` is the number whose decimal digits are those of `k` reversed (leading zeros dropped),
and `phi` is Euler's totient. The terms are the positive `k` with `phi(rev(k)) = k`:
`1, 12, 36, 192, 1992, 2016, 31067664, …` (the definition reproduces the terms below `2100`,
checked with `#eval`).

Conjecture (Ray Chandler, Jul 20 2003): the sequence is infinite. (Chandler notes that
`2(10^j - 4)` is a term whenever `10^j - 3` is prime, so infinitely many primes `10^j - 3` would
suffice; Farideh Firoozbakht gives a larger family. Neither is known to be infinite.)
-/

namespace OMA.S_oeis_a085331

/-- Decimal reversal. -/
def rev (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

theorem main : {k : ℕ | 0 < k ∧ Nat.totient (rev k) = k}.Infinite := by
  sorry

end OMA.S_oeis_a085331
