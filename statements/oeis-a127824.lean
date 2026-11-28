import Mathlib

/-!
# A127824: the second highest cluster of numbers with Collatz total stopping time n

Source: https://oeis.org/A127824
Credit: @Solfanbtc

A127824: row `n` (offset 0) is the sorted list `T(n, 1) < … < T(n, k_n)` of all numbers with
total stopping time `n` in the Collatz (3x+1) iteration, i.e. reaching `1` for the first time
after exactly `n` steps of `x ↦ x/2` (x even), `x ↦ 3x + 1` (x odd).

The entry's Collatz-conjecture remark (every positive integer occurs in some row) is the Collatz
conjecture, already stated upstream, and is not repeated here. The other conjecture (M. Sigg,
Sep 25 2020) begins with a qualitative description ("non-overlapping clusters of numbers which
have the same order of magnitude"), which has no precise meaning; its precise part is:

  "The second highest cluster of row n consists of the numbers
  T(n, k_n - r) = 4^(r - 1) * t(n - 2*r + 2) for 1 <= r <= (n - 3) / 2,
  where t(k) = (2^k - (-1)^k - 3) / 6."

`main` states this precise identity: for `r ≥ 1` with `r ≤ (n - 3)/2` (i.e. `2r + 3 ≤ n`), the
number `m = 4^(r-1) t(n - 2r + 2)` has total stopping time `n`, and exactly `r` numbers with
total stopping time `n` are larger than `m` (so `m = T(n, k_n - r)`; the largest one is `2^n`).
Rows are finite (their elements are at most `2^n`). Checked with python3 for all `n ≤ 45`.
-/

namespace OMA.S_oeis_a127824

/-- One step of the Collatz map. -/
def step (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- `m` has total stopping time `n`: it reaches `1` for the first time after `n` steps. -/
def HasStoppingTime (m n : ℕ) : Prop :=
  step^[n] m = 1 ∧ ∀ j < n, step^[j] m ≠ 1

/-- `t(k) = (2^k - (-1)^k - 3)/6` (an integer for `k ≥ 1`). -/
def t (k : ℕ) : ℤ := (2 ^ k - (-1) ^ k - 3) / 6

/-- Sigg's conjecture: `T(n, k_n - r) = 4^(r-1) t(n - 2r + 2)` for `1 ≤ r ≤ (n - 3)/2`. -/
theorem main : ∀ n r : ℕ, 1 ≤ r → 2 * r + 3 ≤ n →
    ∃ m : ℕ, (m : ℤ) = 4 ^ (r - 1) * t (n - 2 * r + 2) ∧ 0 < m ∧ HasStoppingTime m n ∧
      {x : ℕ | 0 < x ∧ HasStoppingTime x n ∧ m < x}.ncard = r := by
  sorry

end OMA.S_oeis_a127824
