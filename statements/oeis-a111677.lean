import Mathlib

/-!
# A111677: Array of primes of the type k concatenated with 2n-1 where k < 2n-1. Sequence contains the number of terms in the n-th rows.

Source: https://oeis.org/A111677
Credit: @Solfanbtc

Conjecture (entry comment, corrected by R. J. Mathar, Aug 20 2007): a(n) = 0 iff n ≡ 3 (mod 5).

Definitions. Row n consists of the primes obtained by writing some k with 1 ≤ k < 2n - 1 in
decimal followed by the decimal digits of 2n - 1, i.e. `k * 10^d + (2n - 1)` with `d` the
number of decimal digits of `2n - 1` (Maple program of the entry); a(n) (offset 1) is the
number of such k. This reproduces all 79 data terms (python3, `#eval` for the first 30).

Range fix. At n = 1 there is no k with 1 ≤ k < 1, so a(1) = 0 (the first data term) although
1 ≢ 3 (mod 5); the iff therefore fails at that trivial value, and the minimal fix is to state
it for n ≥ 2. (The direction "n ≡ 3 (mod 5) → a(n) = 0" is immediate: 2n - 1 then ends in 5.)
python3: for 2 ≤ n < 3000, a(n) = 0 exactly when n ≡ 3 (mod 5).
-/

namespace OMA.S_oeis_a111677

/-- A111677(n): number of `k`, `1 ≤ k < 2n - 1`, such that `k` concatenated with `2n - 1` is
prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (2 * n - 1)).filter fun k =>
    (k * 10 ^ (Nat.digits 10 (2 * n - 1)).length + (2 * n - 1)).Prime).card

theorem main : ∀ n : ℕ, 2 ≤ n → (a n = 0 ↔ n % 5 = 3) := by
  sorry

end OMA.S_oeis_a111677
