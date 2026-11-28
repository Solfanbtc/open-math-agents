import Mathlib

/-!
# A056929: Difference between n^2 and average of smallest prime greater than n^2 and largest prime less than n^2.

Source: https://oeis.org/A056929
Credit: @Solfanbtc

Conjecture (Bill McEachen, OEIS A056929, comment, Dec 12 2022): the most frequent value will be
1 (including sequence variants with any even power n^(2k)).

Conventions:
* For m ≥ 4, `v m = m - (p + q)/2`, where p is the smallest prime > m and q the largest prime
  < m (both odd, so p + q is even and the average is an integer). A056929(n) = v(n^2) for
  n ≥ 2 (offset 2); the variant for the even power 2k is n ↦ v(n^(2k)), n ≥ 2, k ≥ 1 (k = 1 is
  this sequence).
* "The most frequent value will be 1" is read as: from some point on, 1 is strictly the most
  frequent value. There is N0 such that for every N ≥ N0 and every integer w ≠ 1, w occurs among
  the first terms (n = 2..N) strictly fewer times than 1. (The values are unbounded, so
  frequencies are compared as counts among the first N terms.)
* Checked in Python (Miller-Rabin): `v` reproduces %S; for n^2 and 2 ≤ n ≤ 10^5, 1 is the unique
  most frequent value for every N > 64 (6932 times, then 0 with 5299 times); for n^4 and
  2 ≤ n ≤ 3·10^4, for every N > 2056.
-/

namespace OMA.S_oeis_a056929

/-- The smallest prime greater than `m`. -/
noncomputable def nextPrime (m : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (m + 1))

/-- The largest prime less than `m` (for `m ≥ 3`). -/
def prevPrime (m : ℕ) : ℕ := Nat.findGreatest (fun q => q.Prime ∧ q < m) m

/-- `m` minus the average of the primes around `m`. -/
noncomputable def v (m : ℕ) : ℤ := (m : ℤ) - ((nextPrime m : ℤ) + prevPrime m) / 2

/-- Number of `n ∈ [2, N]` with `v (n^(2k)) = w`. -/
noncomputable def count (k N : ℕ) (w : ℤ) : ℕ :=
  ((Finset.Icc 2 N).filter fun n => v (n ^ (2 * k)) = w).card

/-- McEachen's conjecture: eventually, 1 is strictly the most frequent value, for every even
power `n^(2k)`. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ w : ℤ, w ≠ 1 → count k N w < count k N 1 := by
  sorry

end OMA.S_oeis_a056929
