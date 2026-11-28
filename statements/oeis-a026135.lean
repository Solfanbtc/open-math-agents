import Mathlib

/-!
# A026135: Mathar's recurrence for nonnegative walks from 1 with a forced first ±1 step

Source: https://oeis.org/A026135
Credit: @Solfanbtc

A026135 (offset 0): the number of sequences `(s(0), s(1), …, s(n))` of nonnegative integers with
`s(0) = 1`, `|s(1) - s(0)| = 1`, and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2` (any endpoint).
Data 1, 2, 5, 14, 39, 110, 312, …

Conjecture (R. J. Mathar, Jun 23 2013):
`(n+2) a(n) + 3(-n-1) a(n-1) + (-n-2) a(n-2) + 3(n-3) a(n-3) = 0`,
stated for `n ≥ 3` (so that every index is at least the offset 0).

Checked with python3: the definition reproduces the 15 listed terms and the recurrence holds for
`3 ≤ n < 100`.
-/

namespace OMA.S_oeis_a026135

/-- A026135: the number of such walks of length `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Fin (n + 1) → ℕ | s 0 = 1 ∧
    ∀ i : Fin (n + 1), ∀ hi : 0 < i.val,
      (i.val = 1 → |(s i : ℤ) - s ⟨i.val - 1, by omega⟩| = 1) ∧
      (2 ≤ i.val → |(s i : ℤ) - s ⟨i.val - 1, by omega⟩| ≤ 1)}.ncard

/-- Mathar's recurrence for A026135, for `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n + 3 * (-(n : ℤ) - 1) * a (n - 1) + (-(n : ℤ) - 2) * a (n - 2)
      + 3 * ((n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026135
