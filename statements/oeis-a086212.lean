import Mathlib

/-!
# A086212: Primes in A071998.

Source: https://oeis.org/A086212 (and https://oeis.org/A071998, A007088)
Credit: @Solfanbtc

`B(n)` (A007088) is `n` written in binary and read as a decimal number (`B(5) = 101`).
A071998(n) = `B(B(n))`: "write n in binary, interpret that as a decimal number, convert back to
binary": 0, 1, 1010, 1011, 1100100, 1100101, ... (offset 0). A086212 lists the terms of A071998
that are prime: 1100101, 100110001001011011101111, ...

Conjecture (entry): there are infinitely many primes in A071998. Since `B` is injective, this is
the same as: `B(B(n))` is prime for infinitely many `n`.

Sanity check (python): `B(B(n))` gives the 15 listed terms of A071998; among `n < 20000` there
are 288 prime values, the smallest five being the listed terms of A086212.
-/

namespace OMA.S_oeis_a086212

/-- A007088: the binary digits of `n` read as a decimal number. -/
def B (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 2 n)

/-- The conjecture: infinitely many terms of A071998 are prime. -/
theorem main : Set.Infinite {n : ℕ | (B (B n)).Prime} := by
  sorry

end OMA.S_oeis_a086212
