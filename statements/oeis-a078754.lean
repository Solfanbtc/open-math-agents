import Mathlib

/-!
# A078754: Numbers k such that for all m>k there are more than n primes between m and 2m (inclusive).

Source: https://oeis.org/A078754
Credit: @Solfanbtc

`a(n)` (offset 1) is the least `k` such that every `m > k` has more than `n` primes in the
closed interval `[m, 2m]`. (The PARI program returns the largest `m` with exactly `n` such
primes. This is the same number: the count changes by at most 1 from `m` to `m + 1`.) For
example `a(3) = 14`.

Comment in the entry: "The terms shown are only conjectured values": each term is a claim
about all `m > k`. `main` states that the 56 listed terms are correct. Checked with python3
(sieve): for all `m ≤ 10^6` the counts give exactly these values, and for `5000 ≤ m ≤ 10^6`
every count is at least 559. (Explicit bounds for Ramanujan primes (Sondow; Laishram) should
make these values provable.)
-/

namespace OMA.S_oeis_a078754

/-- Number of primes `p` with `m ≤ p ≤ 2m`. -/
def primesBetween (m : ℕ) : ℕ := ((Finset.Icc m (2 * m)).filter Nat.Prime).card

/-- The listed terms `a(1), …, a(56)`. -/
def data : List ℕ :=
  [1, 8, 14, 20, 21, 26, 33, 35, 48, 50, 51, 63, 74, 75, 81, 86, 90, 111, 114, 116, 119, 120,
    128, 134, 140, 153, 155, 168, 174, 183, 186, 200, 204, 209, 215, 216, 219, 230, 243,
    245, 249, 284, 285, 288, 296, 299, 300, 303, 320, 321, 323, 326, 329, 338, 354, 363]

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≤ data.length →
      IsLeast {k : ℕ | ∀ m : ℕ, k < m → n < primesBetween m} (data.getD (n - 1) 0) := by
  sorry

end OMA.S_oeis_a078754
