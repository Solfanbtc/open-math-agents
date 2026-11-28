import Mathlib

/-!
# A094960: Positive integers k such that the derivative of the k-th Bernoulli polynomial B(k,x) contains only integer coefficients.

Source: https://oeis.org/A094960
Credit: @Solfanbtc

Conjectures recorded in the entry:
1. (Max Alekseyev, Jun 04 2012) For every integer k > 78 there exists a prime p >= 3 such that
   the sum of the last two base-p digits of k is at least p.
2. The sequence is finite and 60 is its last term (Alekseyev: implied by 1; Kellner, Oct 02 2023:
   the sequence is proved finite, "it remains to show that 60 is the last term"). With the listed
   terms (no others below 10^9) this says that the sequence is exactly
   {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}.
`main` states both.

Conventions. The last two base-p digits of k are b = k mod p and a = floor(k/p) mod p (a = 0 when
k < p). `Polynomial.bernoulli k` is Mathlib's Bernoulli polynomial (B(6,x) = x^6 - 3x^5 +
(5/2)x^4 - (1/2)x^2 + 1/42 as in the example of the entry); "only integer coefficients" means every
coefficient of its derivative is an integer. Checked numerically: the k < 300 in the sequence are
exactly the ten listed terms (via k binomial(k-1, m) B_m, the coefficients of the derivative), and
1 holds for 79 <= k < 200000.
-/

namespace OMA.S_oeis_a094960

/-- The derivative of the k-th Bernoulli polynomial has only integer coefficients. -/
def HasIntegerDerivative (k : ℕ) : Prop :=
  ∀ i : ℕ, ∃ z : ℤ, (Polynomial.derivative (Polynomial.bernoulli k)).coeff i = z

theorem main :
    (∀ k : ℕ, 78 < k → ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≤ k % p + (k / p) % p) ∧
    {k : ℕ | 0 < k ∧ HasIntegerDerivative k} = ({1, 2, 4, 6, 10, 12, 28, 30, 36, 60} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a094960
