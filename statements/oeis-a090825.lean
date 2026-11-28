import Mathlib

/-!
# A090825: nonprimes n with (3/2)(1/n)(2n+1)(3^n+1)B(2n) an integer

Source: https://oeis.org/A090825
Credit: @Solfanbtc

With `B(k)` the Bernoulli numbers (for even index `2n ≥ 2` the convention for `B(1)` is irrelevant;
Mathlib's `bernoulli`), let `V(n) = (3/2)(1/n)(2n+1)(3^n+1)B(2n)`. A090825: nonprimes `n ≥ 1` with
`V(n)` an integer: `1, 49, 91, 119, 133, 169, 217, …` (an exact computation reproduces all 18 data
terms).

Conjecture (OEIS comment): composite numbers with all prime factors in A053176 are in the sequence,
where A053176 is the primes `p` such that `2p + 1` is composite (`7, 13, 17, 19, 31, …`). Stated as:
for every composite `n` all of whose prime factors `p` satisfy `2p + 1` not prime, `V(n)` is an
integer. (Python: holds for `n < 420`.) The further remarks of the comment (on `V(p) mod p` for
primes, and the question whether the terms with `V(n) ≡ 1 (mod n)` are finitely many) are not
stated.
-/

namespace OMA.S_oeis_a090825

/-- `V(n) = (3/2)(1/n)(2n+1)(3^n+1) B(2n)`. -/
def V (n : ℕ) : ℚ := 3 / 2 * (1 / n) * (2 * n + 1) * (3 ^ n + 1) * bernoulli (2 * n)

/-- Composite `n` whose prime factors all lie in A053176 are terms of A090825. -/
theorem main : ∀ n : ℕ, 1 < n → ¬ n.Prime →
    (∀ p ∈ n.primeFactors, ¬ (2 * p + 1).Prime) → (V n).den = 1 := by
  sorry

end OMA.S_oeis_a090825
