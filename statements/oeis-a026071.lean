import Mathlib

/-!
# A026071: Mathar's recurrence for walks from 0 to 4 with two forced ±1 first steps

Source: https://oeis.org/A026071
Credit: @Solfanbtc

A026071 (offset 4): `a(n)` is the number of integer sequences `(s(0), s(1), …, s(n))` with
`s(0) = 0`, `|s(i) - s(i-1)| = 1` for `i = 1, 2`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 3`, and
`s(n) = 4`. Data 1, 3, 12, 40, 133, 427, …

Conjecture (R. J. Mathar, Jun 22 2013):
`-(n-4)(n+4) a(n) + (4n+7)(n-4) a(n-1) + (-2n^2+23n-12) a(n-2) - (4n+3)(n-4) a(n-3)
 + 3(n-4)(n-5) a(n-4) = 0`,
stated for `n ≥ 8` (so that every index is at least the offset 4).

Checked with python3: the definition reproduces the 13 listed terms and the recurrence holds for
`8 ≤ n < 90`.
-/

namespace OMA.S_oeis_a026071

/-- A026071: the number of such integer walks `s(0), …, s(n)` from `0` to `4`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Fin (n + 1) → ℤ | s 0 = 0 ∧ s (Fin.last n) = 4 ∧
    ∀ i : Fin (n + 1), ∀ hi : 0 < i.val,
      (i.val ≤ 2 → |s i - s ⟨i.val - 1, by omega⟩| = 1) ∧
      (3 ≤ i.val → |s i - s ⟨i.val - 1, by omega⟩| ≤ 1)}.ncard

/-- Mathar's recurrence for A026071, for `n ≥ 8`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) - 4) * (n + 4) * a n + (4 * (n : ℤ) + 7) * (n - 4) * a (n - 1)
      + (-2 * (n : ℤ) ^ 2 + 23 * n - 12) * a (n - 2) - (4 * (n : ℤ) + 3) * (n - 4) * a (n - 3)
      + 3 * ((n : ℤ) - 4) * (n - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026071
