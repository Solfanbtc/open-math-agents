import Mathlib

/-!
# A103513: Primes of the form primorial(P(k))/2-2^n with minimal n, n>=0, k>=2.

Source: https://oeis.org/A103513
Credit: @Solfanbtc

Conjecture (Lei Zhou, OEIS A103513, %C line): the sequence is defined for all `k ≥ 2`, i.e. for
every `k ≥ 2` there is an `n ≥ 0` such that `primorial(P(k))/2 - 2^n` is prime, where `P(k)` is
the `k`-th prime and `primorial(P(k)) = 2 * 3 * 5 * ... * P(k)`.
(`a(k)` is that prime for the least such `n`; e.g. `P(5)#/2 - 2^1 = 1155 - 2 = 1153`.)

Formalization.
* `P(k) = Nat.nth Nat.Prime (k - 1)` (1-indexed: `P(1) = 2`), and Mathlib's `primorial p` is the
  product of the primes `≤ p`, so `primorial (P k)` is the product of the first `k` primes.
* The difference is taken in `ℕ`; a truncated value `0` (when `2^n` exceeds the primorial half)
  is not prime, so only genuine positive differences count.

Checked with python3 (Miller-Rabin): the least such `n` gives all listed %S/%T/%U terms
(`k = 2, ..., 18`), and some `n` works for every `k ≤ 46` (`P(k) < 200`).
-/

namespace OMA.S_oeis_a103513

/-- For every `k ≥ 2` some `primorial(P(k))/2 - 2^n` is prime. -/
theorem main : ∀ k : ℕ, 2 ≤ k →
    ∃ n : ℕ, (primorial (Nat.nth Nat.Prime (k - 1)) / 2 - 2 ^ n).Prime := by
  sorry

end OMA.S_oeis_a103513
