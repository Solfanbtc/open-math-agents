import Mathlib

/-!
# A110074: Numbers n such that sigma(n) = 2n - 3*phi(phi(n)).

Source: https://oeis.org/A110074
Credit: @Solfanbtc

Conjecture (Farideh Firoozbakht, in the entry): "The sequence is infinite and 369 is the only
composite term. I checked the validity of this conjecture up to 1.5*10^9."

Formalization.
* `InSeq n` : `n ≥ 1` and `σ(n) = 2n - 3 φ(φ(n))`, computed in `ℤ` (the right side may be
  negative, e.g. at n = 1, where it is -1, so 1 is not a term).
* "composite" means `n > 1` and not prime; since 1 is not a term, the second part reads: every
  term that is not prime equals 369.
* The two parts are stated as one conjunction, as in the source.
Checked with python3: the terms up to 2*10^6 are exactly the 40 data terms 7, 13, 19, 37, ...,
1769473, and 369 is the only non-prime among them. (The entry notes that every prime
2^k 3^j + 1 with k, j ≥ 1 is a term; the infinitude part is not implied by the upstream
statement that there are infinitely many Pierpont primes 2^a 3^b + 1, a, b ≥ 0, and the
composite part is independent of it.)
-/

namespace OMA.S_oeis_a110074

/-- `n` is a term of A110074. -/
def InSeq (n : ℕ) : Prop :=
  1 ≤ n ∧ ((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) = 2 * n - 3 * (Nat.totient (Nat.totient n) : ℤ)

theorem main :
    {n : ℕ | InSeq n}.Infinite ∧ ∀ n : ℕ, InSeq n → ¬ n.Prime → n = 369 := by
  sorry

end OMA.S_oeis_a110074
