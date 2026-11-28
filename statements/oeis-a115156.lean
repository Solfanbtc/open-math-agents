import Mathlib

/-!
# A115156: for every n, some number has n binary ones and n prime factors

Source: https://oeis.org/A115156 (with https://oeis.org/A061712)
`a(n)` (offset 1) is the smallest number having exactly `n` ones in binary representation and
also exactly `n` prime factors counted with multiplicity: 2, 6, 28, 54, 405, 486, 2808, ...
The entry asks (Charles R Greathouse IV, Jul 30 2011): "Does a(n) exist for every n? It exists
for large enough n due to a result of Drmota, Mauduit, & Rivat, see A061712. T. D. Noe's
conjecture there implies that a(n) < 4*4^n."

We state the positive answer to the question: for every `n ≥ 1` there is a number `m` with
exactly `n` ones in binary and `Ω(m) = n` (then `a(n)` is the least such `m`).
Remark: if a prime `p` with exactly `n` binary ones exists, then `m = 2^(n-1) p` works, which is
how the Drmota-Mauduit-Rivat theorem on primes with prescribed binary digit sum gives the
statement for all large `n`.
Conventions. `Nat.digits 2 m` lists the binary digits (no leading zeros); `Ω` is
`ArithmeticFunction.cardFactors`.
Checked: the 27 listed terms satisfy both conditions (e.g. `405 = 3^4·5 = 110010101₂`).

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a115156

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, (Nat.digits 2 m).count 1 = n ∧ ArithmeticFunction.cardFactors m = n := by
  sorry

end OMA.S_oeis_a115156
