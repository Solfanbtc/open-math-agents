import Mathlib

/-!
# A053033: Numbers which are the average of two primes in more ways than any smaller number.

Source: https://oeis.org/A053033
Credit: @Solfanbtc

Conjectures stated (OEIS A053033, comments):
1. (Ahmad J. Masad, Dec 09 2019, Conjecture 2) If this sequence is infinite, then for each
   prime number p > 2, there exists a minimum sufficiently large number k such that all terms
   >= k are multiples of p.
2. (Hugo Pfoertner, Dec 09 2019) Apparently, all terms >= 90 are multiples of 15.
`main` is the conjunction of 1 and 2.
Masad's Conjecture 1 (the sequence is infinite) is not restated: it is implied by
`statements/oeis-a045917.lean` (every m ≥ 0 is a value of A045917, so A045917 is unbounded and
has infinitely many records).

Conventions:
* `g n` = A045917(n) = number of unordered pairs of primes {p, q} with p + q = 2n, i.e. the
  number of ways n is the average of two primes (counted as p ≤ n with p and 2n - p prime).
* The terms are the positive integers `n` with `g n > g m` for every `1 ≤ m < n` (records of
  A045917 over the positive integers, so a(1) = 1 with g(1) = 0).
* "a minimum sufficiently large number k" only matters through existence: some `k` such that
  every term `≥ k` is divisible by `p`.
* Checked in Python: these records reproduce every term of %S, %T, %U; up to 2·10^6 there are
  210 records, all records ≥ 90 are multiples of 15, and the last record not divisible by
  3, 5, 7, 11, 13 is 17, 84, 825, 672945, 1865325.
-/

namespace OMA.S_oeis_a053033

/-- A045917: the number of ways to write `n` as the average of two primes. -/
def g (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun p => p.Prime ∧ (2 * n - p).Prime).card

/-- `n` is a term of A053033: a record of `g` among the positive integers. -/
def IsTerm (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → g m < g n

/-- Masad's Conjecture 2 and Pfoertner's observation. -/
theorem main :
    ({n | IsTerm n}.Infinite →
        ∀ p : ℕ, p.Prime → 2 < p → ∃ k : ℕ, ∀ n, IsTerm n → k ≤ n → p ∣ n) ∧
    (∀ n, IsTerm n → 90 ≤ n → 15 ∣ n) := by
  sorry

end OMA.S_oeis_a053033
