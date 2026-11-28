import Mathlib

/-!
# A077038: Least difference of primes p, q such that p < n^3 < q.

Source: https://oeis.org/A077038
Credit: @Solfanbtc

Conjecture (OEIS A077038): every even integer greater than 2 occurs infinitely often in this
sequence.

Definition (offset 2): a(n) = q - p for the primes p < n^3 < q with q - p least, i.e. p the largest
prime below n^3 and q the least prime above (n^3 is not prime for n >= 2), so p and q are
consecutive primes. `HasGap n m` says that a(n) = m. Checked numerically: the listed terms
4, 6, 6, 14, 12, ... are reproduced, and a(n) = 4 for n = 2, 129, 189, 369, 435, 549, 555, 561, 819
below 1000, as stated in the entry.
-/

namespace OMA.S_oeis_a077038

/-- a(n) = m: consecutive primes p < n^3 < q with q - p = m. -/
def HasGap (n m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < n ^ 3 ∧ n ^ 3 < q ∧ q = p + m ∧
    ∀ r : ℕ, p < r → r < q → ¬ r.Prime

theorem main : ∀ m : ℕ, Even m → 2 < m → {n : ℕ | 2 ≤ n ∧ HasGap n m}.Infinite := by
  sorry

end OMA.S_oeis_a077038
