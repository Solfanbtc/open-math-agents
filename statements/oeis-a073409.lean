import Mathlib

/-!
# A073409: Largest prime factor of the denominator of the Bernoulli number B(2*n) (A002445).

Source: https://oeis.org/A073409
Credit: @Solfanbtc

Conjecture (Thomas Ordowski, May 17 2020, OEIS A073409): for n > 0, a(n) is the largest prime
p <= 2n+1 such that p * A000367(n) ≡ -A002445(n) (mod p^2), where A000367(n) and A002445(n) are the
numerator and denominator of B(2n).

Translation: B(2n) is Mathlib's `bernoulli (2 * n)` (a rational; B(2n) does not depend on the sign
convention for B(1)); its numerator (signed, as in A000367) and denominator are `Rat.num` and
`Rat.den` of the reduced fraction. a(n) is the largest prime factor of the denominator. `main`
says that a(n) is the greatest element of the set of primes p <= 2n+1 with
p^2 ∣ p * num + den (in ℤ).
Checked numerically for 1 <= n < 200.
-/

namespace OMA.S_oeis_a073409

/-- a(n): the largest prime factor of the denominator of B(2n). -/
def IsA073409 (n p : ℕ) : Prop :=
  IsGreatest {q : ℕ | q.Prime ∧ q ∣ (bernoulli (2 * n)).den} p

theorem main : ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, IsA073409 n p →
    IsGreatest {q : ℕ | q.Prime ∧ q ≤ 2 * n + 1 ∧
      ((q : ℤ) ^ 2 ∣ (q : ℤ) * (bernoulli (2 * n)).num + ((bernoulli (2 * n)).den : ℤ))} p := by
  sorry

end OMA.S_oeis_a073409
