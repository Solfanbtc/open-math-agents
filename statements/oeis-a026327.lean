import Mathlib

/-!
# A026327: Mathar's recurrence for nonnegative Motzkin-type walks from 2 to 4

Source: https://oeis.org/A026327
Credit: @Solfanbtc

A026327 (offset 2): `a(n)` is the number of sequences `(s(0), s(1), …, s(n))` of nonnegative
integers with `|s(i) - s(i-1)| ≤ 1` for `i = 1, …, n`, `s(0) = 2` and `s(n) = 4`.
Data 1, 3, 10, 30, 90, 266, 783, …

Conjecture (R. J. Mathar, Jun 23 2013):
`-(n+8)(n-2) a(n) + 3(2n^2 + 7n - 28) a(n-1) + 3(-3n^2 - n + 36) a(n-2)
 - 4(n+4)(n-1) a(n-3) + 12(n-1)(n-2) a(n-4) = 0`,
stated for `n ≥ 6` (so that every index is at least the offset 2).

Checked with python3: the definition reproduces the 14 listed terms and the recurrence holds for
`6 ≤ n < 90`.
-/

namespace OMA.S_oeis_a026327

/-- A026327: the number of walks `s(0), …, s(n)` on `ℕ` with steps in `{-1, 0, 1}` from `2`
to `4`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Fin (n + 1) → ℕ | s 0 = 2 ∧ s (Fin.last n) = 4 ∧
    ∀ i : Fin (n + 1), ∀ hi : 0 < i.val, |(s i : ℤ) - s ⟨i.val - 1, by omega⟩| ≤ 1}.ncard

/-- Mathar's recurrence for A026327, for `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 8) * (n - 2) * a n + 3 * (2 * (n : ℤ) ^ 2 + 7 * n - 28) * a (n - 1)
      + 3 * (-3 * (n : ℤ) ^ 2 - n + 36) * a (n - 2) - 4 * ((n : ℤ) + 4) * (n - 1) * a (n - 3)
      + 12 * ((n : ℤ) - 1) * (n - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026327
