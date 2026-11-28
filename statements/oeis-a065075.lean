import Mathlib

/-!
# A065075: Sum of digits of the sum of the preceding numbers.

Source: https://oeis.org/A065075 (see A230289, A004207)
Credit: @Solfanbtc

`a(1) = 1` and, for `n ≥ 2`, `a(n)` is the sum of the decimal digits of `a(1) + ... + a(n-1)`:
1, 1, 2, 4, 8, 7, 5, 10, 11, 13, 8, 7, 14, ... (offset 1). No term is a multiple of 3 (the
digital roots cycle through 1, 2, 4, 8, 7, 5).

Conjecture (Franklin T. Adams-Watters, Jun 29 2009; see A230289): every positive integer that is
not a multiple of 3 appears in the sequence.

Encoding: `S n = a(1) + ... + a(n)` (`S 0 = 0`), `a 1 = 1`, `a (n + 2)` is the digit sum of
`S (n + 1)`.

Sanity check (python): the definition reproduces all 77 listed terms; within the first `2·10^6`
terms every non-multiple of 3 below 65 occurs, at the positions listed in A230289
(1, 3, 4, 7, 6, 5, 8, 9, 10, 13, 24, 41, 26, 51, ...).
-/

namespace OMA.S_oeis_a065075

/-- `S n = a(1) + ... + a(n)`. -/
def S : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => S (n + 1) + (Nat.digits 10 (S (n + 1))).sum

/-- A065075 (indexed from 1). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (Nat.digits 10 (S (n + 1))).sum

/-- Adams-Watters's conjecture: every positive non-multiple of 3 is a term. -/
theorem main : ∀ m : ℕ, 0 < m → ¬ 3 ∣ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a065075
