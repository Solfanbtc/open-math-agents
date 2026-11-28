import Mathlib

/-!
# A069482: a(n) = prime(n+1)^2 - prime(n)^2.

Source: https://oeis.org/A069482 (sopfr: A001414)
Credit: @Solfanbtc

`a(n) = prime(n+1)^2 - prime(n)^2` (offset 1, `prime(1) = 2`): 5, 16, 24, 72, 48, 120, 72, ...
`sopfr(m)` (A001414) is the sum of the prime factors of `m` with repetition; it takes every value
`≥ 2` (at primes) and never 0 or 1 for `m ≥ 2`.

Conjectures of Richard R. Forberg recorded in the entry (stated as a conjunction):
1. (Feb 07 2015) `sopfr(a(n))` "covers all integers covered by sopfr, except 2,3,4,6,7,10,13,15",
   i.e. `{sopfr(a(n)) : n ≥ 1}` is the set of integers `≥ 2` other than 2, 3, 4, 6, 7, 10, 13, 15;
2. (Feb 17 2015) "There is no upper bound on the number of repetitions (i.e., size of a tally)
   that will occur for some a(n) values": for every `T` some value is taken by `a` at least `T`
   times. (Each value is taken only finitely often, since `a(n) > prime(n)`, so the count is a
   finite cardinality.)

Sanity check (python): over the first 300000 terms, the values of `sopfr(a(n))` below 400 are all
integers in `[2, 400)` except exactly 2, 3, 4, 6, 7, 10, 13, 15; over the primes below `2·10^7`,
values of `a` repeat up to 4 times (the entry reports tally 5 first at `a = 187117320`).
-/

namespace OMA.S_oeis_a069482

/-- `a(n) = prime(n+1)^2 - prime(n)^2` for `n ≥ 1` (`Nat.nth Nat.Prime 0 = 2`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Nat.Prime n ^ 2 - Nat.nth Nat.Prime (n - 1) ^ 2

/-- Sum of prime factors with repetition (A001414). -/
def sopfr (m : ℕ) : ℕ := m.primeFactorsList.sum

/-- Forberg's two conjectures. -/
theorem main :
    {s : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sopfr (a n) = s} =
      {s : ℕ | 2 ≤ s ∧ s ∉ ({2, 3, 4, 6, 7, 10, 13, 15} : Finset ℕ)} ∧
    ∀ T : ℕ, ∃ v : ℕ, T ≤ {n : ℕ | 1 ≤ n ∧ a n = v}.ncard := by
  sorry

end OMA.S_oeis_a069482
