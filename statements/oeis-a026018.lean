import Mathlib

/-!
# A026018: a(n) = number of (s(0), s(1), ..., s(2*n-1)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n, s(0) = 2, s(2*n-1) = 7.

Source: https://oeis.org/A026018
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 20 2013, OEIS A026018): for n >= 6 (offset 3, so that a(n-3) is a
term),
  -(n+5)(3n-37) a(n) + 3(-n^2-84n-173) a(n-1) + 2(32n^2+295n+254) a(n-2) - 8(n+25)(2n-5) a(n-3) = 0.

Definition. The name says |s(i) - s(i-1)| = 1 "for i = 1,2,...,n"; since the string has length
2n and the data (a(3) = 1: the single all-up string 2, 3, 4, 5, 6, 7) count strings whose every
step is ±1, the condition is read for i = 1, ..., 2n-1 (the only reading matching the data).
A string is determined by its 2n-1 steps (`true` ↦ +1, `false` ↦ -1); s(i) is 2 plus the sum
of the first i steps, it must stay >= 0 for 0 <= i <= 2n-1, and s(2n-1) = 7.
Checked numerically: reproduces all 25 listed terms 1, 7, 36, 164, ... (and agrees with
Eldar's formula binomial(2n-1, n-3) - binomial(2n-1, n-6)); the recurrence holds for 6 <= n < 120.
-/

namespace OMA.S_oeis_a026018

/-- s(i) = 2 + (sum of the first `i` steps). -/
def pos {L : ℕ} (ε : Fin L → Bool) (i : ℕ) : ℤ :=
  2 + ∑ j : Fin L, if (j : ℕ) < i then (if ε j then (1 : ℤ) else -1) else 0

/-- a(n): strings of length 2n with s(0) = 2, steps ±1, all values ≥ 0, s(2n-1) = 7. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun ε : Fin (2 * n - 1) → Bool =>
    (∀ i : Fin (2 * n), 0 ≤ pos ε i) ∧ pos ε (2 * n - 1) = 7).card

theorem main : ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 5) * (3 * n - 37) * a n + 3 * (-(n : ℤ) ^ 2 - 84 * n - 173) * a (n - 1)
      + 2 * (32 * (n : ℤ) ^ 2 + 295 * n + 254) * a (n - 2)
      - 8 * ((n : ℤ) + 25) * (2 * n - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026018
