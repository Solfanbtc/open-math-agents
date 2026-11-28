import Mathlib

/-!
# A143226: Numbers n such that there are more primes between n and 2n than between n^2 and (n+1)^2.

Source: https://oeis.org/A143226
Credit: @Solfanbtc

A143226 lists the `n` with `π(2n) - π(n) > π((n+1)²) - π(n²)` (`π` the prime counting function,
as in the entry's Mathematica program): `42, 55, 56, 58, 69, 77, 80, 119, ...`.

Conjecture (T. D. Noe, Aug 01 2008, in the entry): it appears that this sequence is finite;
searching up to 10⁵, the last `n` appears to be 48717 (and, Aug 04 2008, no other `n ≤ 10⁶`).
Stated as: `48717` is the greatest element of the set (so the set is finite and 48717 is its last
term). (Sondow notes that finiteness, with Bertrand's postulate, would give Legendre's conjecture
for all sufficiently large `n`.)

A python3 check (segmented sieve up to `60001²`): the set has 413 elements `n ≤ 60000`, starting
with the data and ending `..., 32460, 40557, 48717`.

Conventions: "between `n` and `2n`" counts the primes in `(n, 2n]`, i.e. `π(2n) - π(n)`, and
"between `n²` and `(n+1)²`" is `π((n+1)²) - π(n²)`, as in the entry's program.
-/

namespace OMA.S_oeis_a143226

/-- Noe's conjecture: the last term of A143226 is 48717. -/
theorem main : IsGreatest
    {n : ℕ | Nat.primeCounting ((n + 1) ^ 2) - Nat.primeCounting (n ^ 2) <
      Nat.primeCounting (2 * n) - Nat.primeCounting n} 48717 := by
  sorry

end OMA.S_oeis_a143226
