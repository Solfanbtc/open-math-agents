import Mathlib

/-!
# A026580: Mathar's recurrence for the half-row sums of the triangle A026568

Source: https://oeis.org/A026580
Credit: @Solfanbtc

A026568: the irregular triangle `T(n, k)`, `0 ≤ k ≤ 2n`. Its entry gives the combinatorial
description: `T(n, k)` is the number of integer strings `s(0), …, s(n)` with `s(0) = 0`,
`s(n) = n - k`, and for `1 ≤ i ≤ n`: `|s(i) - s(i-1)| ≤ 1` if `s(i-1)` is even,
`|s(i) - s(i-1)| = 1` if `s(i-1)` is odd. We use this as the definition. (The recurrence in the
name of A026568 says "2 <= j <= i - 2", evidently meaning `2 ≤ j ≤ 2i - 2`; the description above
reproduces the rows shown there: [1], [1, 1, 1], [1, 1, 3, 1, 1], [1, 2, 4, 5, 4, 2, 1], ….)
A026580 (offset 0): `a(n) = T(n, 0) + T(n, 1) + … + T(n, n)`; data 1, 2, 5, 12, 30, 75, 189, …

Conjecture (R. J. Mathar, Jun 23 2013):
`n a(n) + (n-2) a(n-1) + (-17n+28) a(n-2) + 5(-n+4) a(n-3) + 2(34n-107) a(n-4)
 + 16(n-5) a(n-5) + 32(-2n+9) a(n-6) = 0`,
stated for `n ≥ 6` (so that every index is at least the offset 0).

Checked with python3: the definition reproduces the 15 listed terms and the recurrence holds for
`6 ≤ n < 100`.
-/

namespace OMA.S_oeis_a026580

/-- A026568: the number of admissible strings `s(0), …, s(n)` from `0` to `n - k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  {s : Fin (n + 1) → ℤ | s 0 = 0 ∧ s (Fin.last n) = (n : ℤ) - k ∧
    ∀ i : Fin (n + 1), ∀ hi : 0 < i.val,
      (Even (s ⟨i.val - 1, by omega⟩) → |s i - s ⟨i.val - 1, by omega⟩| ≤ 1) ∧
      (Odd (s ⟨i.val - 1, by omega⟩) → |s i - s ⟨i.val - 1, by omega⟩| = 1)}.ncard

/-- A026580: `T(n, 0) + … + T(n, n)`. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- Mathar's recurrence for A026580, for `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (n : ℤ) * a n + ((n : ℤ) - 2) * a (n - 1) + (-17 * (n : ℤ) + 28) * a (n - 2)
      + 5 * (-(n : ℤ) + 4) * a (n - 3) + 2 * (34 * (n : ℤ) - 107) * a (n - 4)
      + 16 * ((n : ℤ) - 5) * a (n - 5) + 32 * (-2 * (n : ℤ) + 9) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a026580
