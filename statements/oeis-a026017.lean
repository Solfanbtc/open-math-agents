import Mathlib

/-!
# A026017: Mathar's recurrence for the number of nonnegative walks from 2 to 5

Source: https://oeis.org/A026017
Credit: @Solfanbtc

A026017 (offset 2): `a(n)` is the number of sequences `(s(0), s(1), …, s(2n-1))` of nonnegative
integers with `|s(i) - s(i-1)| = 1`, `s(0) = 2` and `s(2n-1) = 5`. Data 1, 5, 21, 83, 319, …

Reading. The entry's name says "for i = 1,2,...,n"; taken literally, `s(n+1), …, s(2n-2)` would be
unconstrained and the count infinite, so the condition is read for `i = 1, …, 2n-1` (all steps),
which reproduces the data (checked with python3) and agrees with the entry's g.f.
`(1 + x C^3) C^4` and formula `binomial(2n-1, n-2) - binomial(2n-1, n-5)`.

Conjecture (R. J. Mathar, Jun 20 2013):
`(n+4) a(n) + (-8n-17) a(n-1) + (19n+1) a(n-2) + 6(-2n+5) a(n-3) = 0`,
stated for `n ≥ 5` (so that every index is at least the offset 2). Checked with python3 for
`5 ≤ n < 90`.
-/

namespace OMA.S_oeis_a026017

/-- A026017: the number of walks `s(0), …, s(2n-1)` on `ℕ` with steps `±1` from `2` to `5`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Fin (2 * n) → ℕ | ∃ h : 0 < 2 * n,
    s ⟨0, h⟩ = 2 ∧ s ⟨2 * n - 1, by omega⟩ = 5 ∧
    ∀ i : Fin (2 * n), 0 < i.val → ∀ hi : i.val - 1 < 2 * n,
      (s i : ℤ) - s ⟨i.val - 1, hi⟩ = 1 ∨ (s i : ℤ) - s ⟨i.val - 1, hi⟩ = -1}.ncard

/-- Mathar's recurrence for A026017, for `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 4) * a n + (-8 * (n : ℤ) - 17) * a (n - 1) + (19 * (n : ℤ) + 1) * a (n - 2)
      + 6 * (-2 * (n : ℤ) + 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026017
