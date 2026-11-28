import Mathlib

/-!
# A000225: a(n) = 2^n - 1. (Sometimes called Mersenne numbers, although that name is usually reserved for A001348.)

Source: https://oeis.org/A000225
Credit: @Solfanbtc

Conjecture (Chai Wah Wu, Sep 08 2021, OEIS A000225): except for a(2) = 3, the terms of
A000225 are exactly the numbers m such that 2^(m+1) - 2^j - 2^k - 1 is composite for all
0 <= j < k <= m.

We state: for every m, the condition holds iff m = 2^n - 1 for some n and m ≠ 3.

Notes on the translation:
* The subtraction never truncates in ℕ: for j < k ≤ m, 2^j + 2^k + 1 ≤ 2^(m-1) + 2^m + 1 ≤ 2^(m+1).
* m = 0 (= a(0)) satisfies the condition vacuously.
* Minimal fix: for m = 1 (= a(1)) the only value is 2^2 - 1 - 2 - 1 = 0, which is not composite
  in the strict sense, yet 1 is a term. So "composite" is read as "not prime". This changes
  nothing for m ≥ 2: the value 1 only occurs at m = 2 (j = 1, k = 2), and m = 2 fails anyway
  because j = 0, k = 2 gives the prime 2; for m ≥ 3 all values are ≥ 2^(m-1) - 1 ≥ 3.
* Checked numerically for m < 200: the m satisfying the condition are 0, 1, 7, 15, 31, 63, 127.
-/

namespace OMA.S_oeis_a000225

theorem main : ∀ m : ℕ,
    (∀ j k : ℕ, j < k → k ≤ m → ¬ (2 ^ (m + 1) - 2 ^ j - 2 ^ k - 1).Prime) ↔
      ((∃ n : ℕ, m = 2 ^ n - 1) ∧ m ≠ 3) := by
  sorry

end OMA.S_oeis_a000225
