import Mathlib

/-!
# A085917: Least k such that k*2^n - 1 is a semiprime.

Source: https://oeis.org/A085917
Credit: @Solfanbtc

The entry's conjecture concerns `k = 509203`, the conjectured smallest Riesel number (so
`509203 * 2^n - 1` is conjecturally never prime). The `n` with `509203 * 2^n - 1` a semiprime
begin `3, 4, 16, 34, 61, 82, 124, 142, 163, 171, …`.

Conjecture (entry): there are infinitely many semiprimes of this form, i.e. infinitely many `n`
with `509203 * 2^n - 1` a semiprime (a product of exactly two primes, counted with
multiplicity: `Ω = 2`). Checked with python3 (trial division to `10^6` plus Miller-Rabin):
for `n < 40` the semiprime cases are exactly `n = 3, 4, 16, 34`, as listed.
-/

namespace OMA.S_oeis_a085917

/-- `m` is a semiprime: it has exactly two prime factors counted with multiplicity. -/
def IsSemiprime (m : ℕ) : Prop := m.primeFactorsList.length = 2

/-- The conjecture: `509203 * 2^n - 1` is a semiprime for infinitely many `n`. -/
theorem main : Set.Infinite {n : ℕ | IsSemiprime (509203 * 2 ^ n - 1)} := by
  sorry

end OMA.S_oeis_a085917
