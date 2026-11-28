import Mathlib

/-!
# A101044: Primes corresponding to A101043 (which is A101042 sorted).

Source: https://oeis.org/A101044
Credit: @Solfanbtc

A020483 (offset 0): `a(n)` is the least prime `p` such that `p + 2n` is also prime. A101044 lists the
primes in the order in which they first appear as values of A020483:
2, 3, 5, 7, 13, 19, 11, 31, 29, 23, 17, ...

Conjecture (in the entry): all primes are in this sequence, i.e. every prime `p` is a value of
A020483: there is `n` with `p + 2n` prime and `q + 2n` not prime for every prime `q < p`
(so that `a(n) = p`). The prime 2 occurs, for `n = 0`.

python3: the data of A101044 is reproduced, and every prime below 200 occurs as `a(n)` for some
`n < 200000`.

Remark: the claim seems to follow from Dirichlet's theorem on primes in arithmetic progressions.
For odd `p`, pick distinct primes `r_q > p` for the odd primes `q < p` and choose `n` with
`2n ≡ -q (mod r_q)` (so `q + 2n` is a proper multiple of `r_q` once `n` is large, and `2 + 2n` is
even and greater than 2); then `p + 2n ≡ p - q ≢ 0 (mod r_q)`, so `p + 2n` runs through an arithmetic
progression whose terms are coprime to its difference, and that progression contains primes.
-/

namespace OMA.S_oeis_a101044

/-- Every prime is the least prime `p` with `p + 2n` prime, for some `n`. -/
theorem main : ∀ p : ℕ, p.Prime →
    ∃ n : ℕ, (p + 2 * n).Prime ∧ ∀ q : ℕ, q < p → q.Prime → ¬ (q + 2 * n).Prime := by
  sorry

end OMA.S_oeis_a101044
