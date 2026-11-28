import Mathlib

/-!
# A079321: Composite numbers of the form 1^1 · 2^2 · 3^3 ⋯ n^n + 1

Source: https://oeis.org/A079321
Credit: @Solfanbtc

With the hyperfactorial `H(n) = 1^1 · 2^2 ⋯ n^n` (A002109; `H(0) = 1`), A079321 lists the
composite numbers `H(n) + 1`: `27649, 86400001, …`. "No primes other than 2, 5, 109 found in this
sequence for `n ≤ 1000`" (`H(1) + 1 = 2`, `H(2) + 1 = 5`, `H(3) + 1 = 109`).

Two conjectures (OEIS comment), stated as the parts of `main`:
1. There are no primes in the sequence `2^2 · 3^3 ⋯ n^n + 1` for `n > 3`: `H(n) + 1` is not prime
   for `n > 3`.
2. There are no primes in the sequence `2^2 · 3^3 ⋯ n^n + 61` for all `n`: `H(n) + 61` is never
   prime (`n ≥ 0`; for `n ≤ 1` it is `62`).
(Python, probable-prime test: `H(n) + 1` is prime only for `n ≤ 3` and `H(n) + 61` never, for
`n < 50`.)
-/

namespace OMA.S_oeis_a079321

/-- The hyperfactorial `H(n) = ∏_{k=1}^{n} k^k`. -/
def H (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, k ^ k

/-- `H(n) + 1` is composite for `n > 3`, and `H(n) + 61` is never prime. -/
theorem main : (∀ n : ℕ, 3 < n → ¬ (H n + 1).Prime) ∧ (∀ n : ℕ, ¬ (H n + 61).Prime) := by
  sorry

end OMA.S_oeis_a079321
