import Mathlib

/-!
# A087713: Greatest prime factor of the product of the neighbors of the n-th prime.

Source: https://oeis.org/A087713 (see A120628)
Credit: @Solfanbtc

`a(n)` is the greatest prime factor of `(p_n - 1)(p_n + 1)`, `p_n` the `n`-th prime:
3, 2, 3, 3, 5, 7, 3, 5, 11, 7, 5, 19, ... (offset 1).
A120628 lists the primes `q` such that `2q` is 1 away from a prime, i.e. `2q - 1` or `2q + 1` is
prime: 2, 3, 5, 7, 11, 19, 23, 29, 31, 37, 41, 53, ...

Conjecture (Jason Yuen, Jan 19 2025): the record values of A087713 are A120628 \ {2}.
A record value is a value `a(n)` with `a(n) > a(m)` for all `1 ≤ m < n` (`a(1) = 3` is the first).

Sanity check (python): the definition gives all 50 listed terms, and for all primes `< 4·10^6`
the 27951 record values are exactly the elements of A120628 \ {2} up to the last record.
-/

namespace OMA.S_oeis_a087713

/-- Greatest prime factor (`0` for `0` and `1`). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- `p_n`, the `n`-th prime (`p_1 = 2`). -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A087713. -/
noncomputable def a (n : ℕ) : ℕ := gpf ((p n - 1) * (p n + 1))

/-- `a(n)` is a record. -/
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → a m < a n

/-- Yuen's conjecture: the record values are the primes `q ≠ 2` with `2q - 1` or `2q + 1`
prime. -/
theorem main :
    {v : ℕ | ∃ n, IsRecord n ∧ a n = v} =
      {q : ℕ | q.Prime ∧ q ≠ 2 ∧ ((2 * q - 1).Prime ∨ (2 * q + 1).Prime)} := by
  sorry

end OMA.S_oeis_a087713
