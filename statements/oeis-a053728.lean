import Mathlib

/-!
# A053728: every prime other than 2 and 5 is the sum of the aliquot divisors of some n

Source: https://oeis.org/A053728
Credit: @Solfanbtc

A053728: for `n = 1, 2, 3, …` compute the sum `s(n) = sigma(n) - n` of the aliquot divisors of
`n`; if it is prime, append it to the sequence.

The entry (R. Israel, Mar 26 2018): "If p is a prime > 7, a slightly stronger form of the Goldbach
conjecture implies there are two distinct primes q,r such that p-1=q+r. Then
sigma(q*r)-q*r=q+r+1=p. Thus every prime > 7 should appear at least once in this sequence. The
primes 3=a(1) and 7=a(2) also appear, but 2 and 5 do not."

`main` states the resulting conjecture: the primes occurring in A053728, i.e. the primes of the
form `s(n)` (`n ≥ 1`), are exactly the primes other than 2 and 5. (It is implied by, and weaker
than, the conjecture that 5 is the only odd untouchable number, stated upstream in
`UntouchableNumber`.) Checked with python3: among the primes below 1400 exactly 2 and 5 are not
of the form `s(n)` (conclusive in this range, since `s(n) > sqrt(n)` for composite `n`).
-/

namespace OMA.S_oeis_a053728

/-- The sum of the aliquot divisors of `n` (A001065). -/
def s (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- The conjecture: a prime is an aliquot sum iff it is neither 2 nor 5. -/
theorem main : ∀ p : ℕ, p.Prime → ((∃ n : ℕ, 1 ≤ n ∧ s n = p) ↔ p ≠ 2 ∧ p ≠ 5) := by
  sorry

end OMA.S_oeis_a053728
