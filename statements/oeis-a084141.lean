import Mathlib

/-!
# A084141: n with exactly one m having exactly n primes between m and 2m

Source: https://oeis.org/A084141
Credit: @Solfanbtc

A060715(m) is the number of primes strictly between `m` and `2m` (`m ≥ 1`); A084138(n) is the number
of `m ≥ 1` with exactly `n` such primes (finite, since `π(2m) - π(m) → ∞`); A084141 lists the `n`
with A084138(n) = 1, i.e. there is exactly one `m > 0` with exactly `n` primes between `m` and `2m`
exclusively: `0, 22, 36, 47, 79, 98, …` (a computation reproduces all 36 data terms).

Conjecture (OEIS comment): there are an infinite number of terms in this sequence.
-/

namespace OMA.S_oeis_a084141

/-- A060715: the number of primes strictly between `m` and `2m`. -/
def primesBetween (m : ℕ) : ℕ := ((Finset.Ioo m (2 * m)).filter Nat.Prime).card

/-- `n` is a term of A084141: exactly one `m ≥ 1` has exactly `n` primes in `(m, 2m)`. -/
def IsTerm (n : ℕ) : Prop := {m : ℕ | 1 ≤ m ∧ primesBetween m = n}.ncard = 1

/-- A084141 is infinite. -/
theorem main : {n : ℕ | IsTerm n}.Infinite := by
  sorry

end OMA.S_oeis_a084141
