import Mathlib

/-!
# A099309: Numbers n whose k-th arithmetic derivative is nonzero for all k. Complement of A099308.

Source: https://oeis.org/A099309
Credit: @Solfanbtc

The arithmetic derivative (A003415): `0' = 1' = 0`, `p' = 1` for primes `p`, `(ab)' = a'b + ab'`;
for `n = ∏ pᵢ^{eᵢ}` it equals `∑ eᵢ · n / pᵢ`.

A099309 lists the `n` with `n^{(k)} ≠ 0` for every `k ≥ 0`. Multiples `m·p^p` of `p^p`
(`p` prime, A051674) stay of that form under differentiation. M. F. Hasler (Apr 09 2015)
conjectured that every other term eventually leads to a term of this form (e.g. 26 → 15 → 8).
Stated here for every term: some iterate `n^{(k)}` (`k = 0` allowed, covering terms that are
already of that form) is divisible by `p^p` for some prime `p`.
Checked numerically: the terms below 3000 computed this way match the OEIS data.
-/

namespace OMA.S_oeis_a099309

/-- The arithmetic derivative A003415 (with `0' = 1' = 0`). -/
def arithDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

theorem main : ∀ n : ℕ, (∀ k : ℕ, arithDeriv^[k] n ≠ 0) →
    ∃ k p : ℕ, p.Prime ∧ p ^ p ∣ arithDeriv^[k] n := by
  sorry

end OMA.S_oeis_a099309
