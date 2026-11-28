import Mathlib

/-!
# A088783: Numbers n such that 10*n^k + 1 is composite for all k > 0.

Source: https://oeis.org/A088783
Credit: @Solfanbtc

A088783 lists the `n` such that `10 n^k + 1` is composite for every `k > 0`:
12, 23, 32, 34, 45, 56, 65, 67, 78, 89, 98, 100, ..., 177.

The entry's formula section states `n = 11m+1 and n = 33m-1 for m > 0`, i.e. the terms are
exactly the numbers `11m + 1` and `33m - 1` with `m > 0`. One inclusion is proved in the
entry: `10 (11m+1)^k + 1` is always divisible by 11, and `10 (33m-1)^k + 1` is divisible by 3
for odd `k` and by 11 for even `k`. The other inclusion is open: it says that every other `n ≥ 1`
has some prime `10 n^k + 1`. The entry lists the open cases below 1024 (185, 338, 417, ...;
`10·185^k + 1` is composite for all `k ≤ 10^6`) and gives the sequence's continuation "if a prime
10*185^k+1 were found". We state this formula as the conjecture: for `n ≥ 1`, `10 n^k + 1` is
composite (i.e. not prime; it is always `≥ 11`) for all `k > 0` iff `n = 11m + 1` or `n = 33m - 1`
for some `m > 0`.

(The desk excerpt also cites the conjectured smallest base-173 Sierpiński number, 28; that is a
different problem, with conventions not stated in the entry, and is not included.)

Sanity check (python): for `1 ≤ n < 185` the numbers of the two forms are exactly the 21 listed
terms; every other `n` in that range has a prime `10 n^k + 1` with `k ≤ 400`, except 17, 101, 142
(primes with larger `k`, as the entry reports for all `n ≤ 1024` outside its open list) and 173
(`10·173^264234 + 1` is prime).
-/

namespace OMA.S_oeis_a088783

/-- The formula of A088783, as a conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∀ k : ℕ, 0 < k → ¬ (10 * n ^ k + 1).Prime) ↔
      ∃ m : ℕ, 0 < m ∧ (n = 11 * m + 1 ∨ n = 33 * m - 1)) := by
  sorry

end OMA.S_oeis_a088783
