import Mathlib

/-!
# A085105: Starting with prime(n) go on adding smaller primes until one gets a prime. a(n) = this prime, or 0 if no such prime exists.

Source: https://oeis.org/A085105
Credit: @Solfanbtc

Starting from `prime(n)`, the next smaller primes `prime(n-1), prime(n-2), …, prime(1) = 2` are
added one at a time (e.g. `13 + 11 + 7 = 31`, so `a(6) = 31`). `a(n)` is the first of the sums
`prime(n) + prime(n-1) + … + prime(n-k)`, `1 ≤ k ≤ n-1`, that is prime, or `0` if none is.
This reproduces every term of %S, %T, %U (Python). Here `prime(i) = Nat.nth Nat.Prime (i - 1)`.

Conjecture (in the entry): "Except a(3) no other term is zero." Read literally this fails at
`n = 1`: `prime(1) = 2` has no smaller prime to add, and the data give `a(1) = 0`. The minimal fix
excludes `n = 1` as well: for every `n ≥ 2` with `n ≠ 3`, some sum
`prime(n) + … + prime(n-k)` with `1 ≤ k ≤ n-1` is prime. (Python: `a(n) = 0` only for `n = 1, 3`
among `n < 4000`.)
-/

namespace OMA.S_oeis_a085105

/-- `prime(i)`, 1-indexed. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

theorem main : ∀ n : ℕ, 2 ≤ n → n ≠ 3 →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n - 1 ∧ (∑ i ∈ Finset.Icc (n - k) n, prime i).Prime := by
  sorry

end OMA.S_oeis_a085105
