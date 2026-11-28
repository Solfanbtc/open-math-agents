import Mathlib

/-!
# A025182: a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is an integer, s(0) = 0, |s(1)| = 1, |s(i) - s(i-1)| <= 1 for i >= 2, s(n) = 4.

Source: https://oeis.org/A025182
Credit: @Solfanbtc

`a(n)` (offset 4) is the number of integer sequences `(s(0), ..., s(n))` with `s(0) = 0`,
`|s(1)| = 1`, `|s(i) - s(i-1)| ≤ 1` for `2 ≤ i ≤ n`, and `s(n) = 4`:
`a(4) = 1, a(5) = 4, a(6) = 16, a(7) = 56, ...`.

Conjectures (R. J. Mathar, Feb 25 2015, in the entry), stated together:
1. `-(n-4)(n+4) a(n) + (4n² - 7n - 29) a(n-1) + (-2n² + 17n - 2) a(n-2)
    - (4n+1)(n-3) a(n-3) + 3(n-3)(n-4) a(n-4) = 0`;
2. `-(n-4)(n+4)(n² - 3n + 6) a(n) + (n-1)(2n³ - 5n² + 11n - 36) a(n-1)
    + 3(n-1)(n-2)(n² - n + 4) a(n-2) = 0`.
Each is stated for the `n` at which all the terms involved are in the sequence's range
(`n ≥ 8` for 1, `n ≥ 6` for 2).

A python3 check (dynamic programming over the paths): the definition reproduces the data, and
both recurrences hold for all `n < 300` (even down to `n = 4`, resp. `n = 2`, with `a(n) = 0`
for `n < 4`).

Conventions:
* A sequence `(s(0), ..., s(n))` is a function `Fin (n + 1) → ℤ`; `a(n)` is the cardinality
  (`Set.ncard`) of the set of such functions with the stated properties (a finite set, since the
  steps are bounded). For `n ≥ 1`, index `1` is `⟨1, _⟩`.
* The recurrences are stated in `ℤ`.
-/

namespace OMA.S_oeis_a025182

/-- The admissible sequences `(s(0), ..., s(n))` (for `n ≥ 1`). -/
def paths (n : ℕ) (hn : 1 ≤ n) : Set (Fin (n + 1) → ℤ) :=
  {s | s 0 = 0 ∧ |s ⟨1, by omega⟩| = 1 ∧
    (∀ i : Fin (n + 1), 2 ≤ i.val → |s i - s ⟨i.val - 1, by omega⟩| ≤ 1) ∧ s (Fin.last n) = 4}

/-- `a n = A025182(n)` for `n ≥ 4` (and `0` for `n = 0`). -/
noncomputable def a (n : ℕ) : ℤ := if hn : 1 ≤ n then ((paths n hn).ncard : ℤ) else 0

/-- Mathar's two conjectured recurrences for A025182. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n →
      -((n : ℤ) - 4) * (n + 4) * a n + (4 * (n : ℤ) ^ 2 - 7 * n - 29) * a (n - 1)
        + (-2 * (n : ℤ) ^ 2 + 17 * n - 2) * a (n - 2) - (4 * (n : ℤ) + 1) * (n - 3) * a (n - 3)
        + 3 * ((n : ℤ) - 3) * (n - 4) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 6 ≤ n →
      -((n : ℤ) - 4) * (n + 4) * ((n : ℤ) ^ 2 - 3 * n + 6) * a n
        + ((n : ℤ) - 1) * (2 * (n : ℤ) ^ 3 - 5 * (n : ℤ) ^ 2 + 11 * n - 36) * a (n - 1)
        + 3 * ((n : ℤ) - 1) * (n - 2) * ((n : ℤ) ^ 2 - n + 4) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a025182
