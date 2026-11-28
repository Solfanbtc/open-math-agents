import Mathlib

/-!
# A077362: Largest n-digit prime whose external digits as well as internal digits form a prime, or 0 if no such number exists.

Source: https://oeis.org/A077362
Credit: @Solfanbtc

An `n`-digit number `p` (`10^(n-1) ≤ p < 10^n`) qualifies when `p` is prime, its external
digits (first and last digit, read as the two-digit number `10 * first + last`) form a prime,
and its internal digits (digits `2, …, n-1`, read as a number, i.e. `(p / 10) % 10^(n-2)`)
form a prime. `a(n)` is the largest qualifying `n`-digit number, or `0` if there is none.

Indexing: the entry lists the offset as `0`, but its data `0, 0, 977, 9677, …` and its
programs index by the number of digits `n = 1, 2, 3, …` (`a(3) = 977`). We index by digit
count, as the name does; this definition reproduces every term of %S, %T, %U
(`n = 1, …, 20`, checked in Python). For `n ≤ 2` there are no internal digits (the internal
value is `0`, not prime), giving the two leading zeros.

Conjecture (Harvey P. Dale, May 26 2018, in the entry): each term after the first two terms
ends with `7`, stated for every digit count `n ≥ 3` (checked in Python for `3 ≤ n < 60`).
The entry's other conjecture, "no entry is zero for n > 2", is the statement of
oma/oeis-a077361 (same definition) and is not repeated here; it also follows from this one,
since `a n % 10 = 7` forces `a n ≠ 0`.
-/

namespace OMA.S_oeis_a077362

/-- `p` is an `n`-digit prime whose external and internal digits form primes. -/
def Good (n p : ℕ) : Prop :=
  10 ^ (n - 1) ≤ p ∧ p < 10 ^ n ∧ p.Prime ∧
    (10 * (p / 10 ^ (n - 1)) + p % 10).Prime ∧ ((p / 10) % 10 ^ (n - 2)).Prime

instance (n p : ℕ) : Decidable (Good n p) := by unfold Good; infer_instance

/-- A077362, indexed by the number of digits: the largest qualifying `n`-digit number, or `0`. -/
def a (n : ℕ) : ℕ := ((Finset.range (10 ^ n)).filter (Good n)).sup id

theorem main : ∀ n : ℕ, 3 ≤ n → a n % 10 = 7 := by
  sorry

end OMA.S_oeis_a077362
