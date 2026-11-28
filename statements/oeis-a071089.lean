import Mathlib

/-!
# A071089: Remainder when sum of first n primes is divided by n-th prime.

Source: https://oeis.org/A071089
Credit: @Solfanbtc

`a(n)` (offset 1) is `(p_1 + ... + p_n) mod p_n`, with `p_1 = 2`. Mathlib's `Nat.nth Nat.Prime`
is 0-indexed (`Nat.nth Nat.Prime 0 = 2`), so `p_i = Nat.nth Nat.Prime (i - 1)`.
Data: 0, 2, 0, 3, 6, 2, 7, 1, 8, 13, ... (the definition reproduces every term of %S, %T, %U).

Conjecture (T. Ordowski, 2013): every nonnegative integer appears in the sequence at most
finitely many times, i.e. for each `m`, the set of `n ≥ 1` with `a(n) = m` is finite.
The entry also records the opposite conjecture (C. R. Greathouse IV, 2013: heuristically each
value appears about `log log x` times below `x`, hence infinitely often); the two contradict each
other, and the statement below is Ordowski's, the conjecture named first.
-/

namespace OMA.S_oeis_a071089

/-- A071089(n), for `n ≥ 1`: the sum of the first `n` primes modulo the `n`-th prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, Nat.nth Nat.Prime i) % Nat.nth Nat.Prime (n - 1)

theorem main : ∀ m : ℕ, {n : ℕ | 1 ≤ n ∧ a n = m}.Finite := by
  sorry

end OMA.S_oeis_a071089
