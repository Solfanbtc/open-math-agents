import Mathlib

/-!
# A056608: Least prime factor of the n-th composite number.

Source: https://oeis.org/A056608
Credit: @Solfanbtc

Conjecture (OEIS A056608): the record values are 2, 3, 5, 7, 11, ...; at each new record the
count of the prior record follows A247509: when prime(k+1) is first seen, there have been
A247509(k) occurrences of prime(k) (3, 3, 2, 4 occurrences of 2, 3, 5, 7 when 3, 5, 7, 11 are first
seen).

Definitions.
* The composite numbers 4, 6, 8, 9, ... are enumerated by `comp j` (j = 0, 1, ...; the entry's
  n-th composite is `comp (n - 1)`), and the least prime factor is `Nat.minFac`.
* A247509(k) is the number of preprimes (A156759, n > 1) whose smallest prime divisor is prime(k).
  Following Shevelev's definition in A156759, a preprime is a composite N whose smallest prime
  factor is the largest prime <= sqrt N (trial division by the primes <= sqrt N finds a divisor
  only at the last step); `IsPreprime` states this as: minFac N ^ 2 <= N and N < q ^ 2 for every
  prime q > minFac N.
* prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1.
`main`: for every k >= 1, prime(k+1) occurs as a value, and if N is the first index at which it
occurs, then the number of indices j < N with value prime(k) equals A247509(k).
Checked numerically for k <= 29 against the 30 listed terms of A247509.
-/

namespace OMA.S_oeis_a056608

/-- The `j`-th composite number, from `j = 0` (`comp 0 = 4`). -/
noncomputable def comp (j : ℕ) : ℕ := Nat.nth (fun m => 1 < m ∧ ¬ m.Prime) j

/-- Shevelev's preprimes: composites whose least prime factor is the largest prime ≤ √N. -/
def IsPreprime (N : ℕ) : Prop :=
  1 < N ∧ ¬ N.Prime ∧ N.minFac ^ 2 ≤ N ∧ ∀ q : ℕ, q.Prime → N.minFac < q → N < q ^ 2

/-- A247509(k): the number of preprimes with smallest prime divisor prime(k). -/
noncomputable def A247509 (k : ℕ) : ℕ :=
  {N : ℕ | IsPreprime N ∧ N.minFac = Nat.nth Nat.Prime (k - 1)}.ncard

theorem main : ∀ k : ℕ, 1 ≤ k →
    (∃ j : ℕ, (comp j).minFac = Nat.nth Nat.Prime k) ∧
    ∀ N : ℕ, IsLeast {j : ℕ | (comp j).minFac = Nat.nth Nat.Prime k} N →
      {j : ℕ | j < N ∧ (comp j).minFac = Nat.nth Nat.Prime (k - 1)}.ncard = A247509 k := by
  sorry

end OMA.S_oeis_a056608
