import Mathlib

/-!
# A037020: Numbers whose sum of proper (or aliquot) divisors is a prime.

Source: https://oeis.org/A037020
Credit: @Solfanbtc

Claim (T. D. Noe, Nov 29 2006, as recorded in the entry): assuming the Goldbach conjecture, all
primes, except 2 and 5, are the sum of the proper divisors of some number.

The claim is conditional, so it is stated as `Goldbach → ...`. "All primes, except 2 and 5" is read
as an exact description: a prime `p` is a sum of proper divisors `s(n) = σ(n) - n` of some `n`
if and only if `p ≠ 2` and `p ≠ 5` (2 and 5 are indeed untouchable, OEIS A005114, so the exceptions
are genuine). A python3 check: every prime `p ≤ 3000` other than 2 and 5 is `s(n)` for some `n`
(searching `n ≤ 3000²`, which suffices since `s(n) > √n` for composite `n`), and 2, 5 are not.

This is distinct from the upstream unconditional conjecture
`UntouchableNumber.unique_odd_untouchable_conjecture` (5 is the only odd untouchable number):
here the hypothesis is Goldbach and the conclusion concerns primes only.

Conventions:
* `s(n) = ∑ d ∈ n.properDivisors, d` (A001065), over all `n : ℕ` (`s(0) = s(1) = 0`, harmless).
* Goldbach's conjecture: every even integer `n > 2` is a sum of two primes (not necessarily
  distinct).
-/

namespace OMA.S_oeis_a037020

/-- Goldbach's conjecture: every even `n > 2` is the sum of two primes. -/
def Goldbach : Prop := ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Assuming Goldbach, the primes that are sums of the proper divisors of some number are exactly
the primes other than 2 and 5. -/
theorem main : Goldbach → ∀ p : ℕ, p.Prime →
    ((∃ n : ℕ, ∑ d ∈ n.properDivisors, d = p) ↔ (p ≠ 2 ∧ p ≠ 5)) := by
  sorry

end OMA.S_oeis_a037020
