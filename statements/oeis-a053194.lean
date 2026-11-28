import Mathlib

/-!
# A053194: a(n) is the smallest number k such that cototient(k) = 2n - 1.

Source: https://oeis.org/A053194
Credit: @Solfanbtc

Question (Thomas Ordowski, OEIS A053194, comment, Oct 07 2016): "Are there infinitely many
semiprimes in the sequence?", stated in its affirmative form: a(n) is a semiprime for
infinitely many n.

Not restated (implied by existing statements): the nonemptiness of the inverse cototient of
every odd number, and the conditional bound a(n) < (2n-1)^2 for n > 3. Both follow from
`statements/oeis-a061357.lean` (every even 2n ≥ 8 is p + q with p ≠ q primes): then
k = pq has cototient p + q - 1 = 2n - 1 and pq < n^2 < (2n-1)^2. The small cases are
cototient(2) = 1, cototient(9) = 3, cototient(25) = 5.

Conventions:
* cototient(k) = k - φ(k) (A051953); a(n) = least k ≥ 1 with cototient(k) = 2n - 1 (offset 1),
  written with `sInf` (if no such k existed, the value 0 would not be a semiprime).
* A semiprime is a product p*q of two primes, p = q allowed (A001358).
* Distinct n give distinct values a(n), since cototient(a(n)) = 2n - 1, so "infinitely many
  semiprimes in the sequence" is the same as infinitely many n with a(n) semiprime.
* Checked in Python: `a` reproduces %S; 221 of a(1..399) are semiprimes.
-/

namespace OMA.S_oeis_a053194

/-- A053194: the least `k ≥ 1` with `k - φ(k) = 2n - 1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ k - k.totient = 2 * n - 1}

/-- Ordowski's question, affirmative form: infinitely many terms are semiprimes. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a n = p * q}.Infinite := by
  sorry

end OMA.S_oeis_a053194
