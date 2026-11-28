import Mathlib

/-!
# A026571: Mathar's recurrence for the strings of A026568 ending at 2

Source: https://oeis.org/A026571
Credit: @Solfanbtc

A026571 (offset 2): `a(n) = T(n, n-2)` with `T` from A026568; equivalently (entry's name) the
number of integer strings `s(0), …, s(n)` counted by `T` with `s(n) = 2`, i.e. with `s(0) = 0`,
`s(n) = 2`, and for `1 ≤ i ≤ n`: `|s(i) - s(i-1)| ≤ 1` if `s(i-1)` is even,
`|s(i) - s(i-1)| = 1` if `s(i-1)` is odd. Data 1, 2, 7, 16, 44, 106, 273, …

Conjecture (R. J. Mathar, Jun 23 2013):
`(n+2) a(n) + 3(-n-1) a(n-1) - 3n a(n-2) + 11(n-1) a(n-3) + 2(n-6) a(n-4) + 4(-2n+7) a(n-5) = 0`,
stated for `n ≥ 7` (so that every index is at least the offset 2).

Checked with python3: the definition reproduces the 14 listed terms and the recurrence holds for
`7 ≤ n < 100`.
-/

namespace OMA.S_oeis_a026571

/-- A026571: the number of admissible strings `s(0), …, s(n)` from `0` to `2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Fin (n + 1) → ℤ | s 0 = 0 ∧ s (Fin.last n) = 2 ∧
    ∀ i : Fin (n + 1), ∀ hi : 0 < i.val,
      (Even (s ⟨i.val - 1, by omega⟩) → |s i - s ⟨i.val - 1, by omega⟩| ≤ 1) ∧
      (Odd (s ⟨i.val - 1, by omega⟩) → |s i - s ⟨i.val - 1, by omega⟩| = 1)}.ncard

/-- Mathar's recurrence for A026571, for `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℤ) + 2) * a n + 3 * (-(n : ℤ) - 1) * a (n - 1) - 3 * (n : ℤ) * a (n - 2)
      + 11 * ((n : ℤ) - 1) * a (n - 3) + 2 * ((n : ℤ) - 6) * a (n - 4)
      + 4 * (-2 * (n : ℤ) + 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026571
