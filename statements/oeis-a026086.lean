import Mathlib

/-!
# A026086: Number of (s(0), s(1), ..., s(n)) such that s(0) = 0, |s(i) - s(i-1)| = 1 for i = 1,2,3; |s(i) - s(i-1)| <= 1 for i >= 4, s(n) = 3

Source: https://oeis.org/A026086
Credit: @Solfanbtc

`a(n)` (offset 4) is the number of integer sequences `(s(0), ..., s(n))` with `s(0) = 0`,
`|s(i) - s(i-1)| = 1` for `i = 1, 2, 3`, `|s(i) - s(i-1)| ≤ 1` for `4 ≤ i ≤ n`, and `s(n) = 3`:
`a(4) = 1, a(5) = 6, a(6) = 16, a(7) = 52, ...`.

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
`(n+3) a(n) - 5(n+1) a(n-1) + 3(n-5) a(n-2) + (11n-9) a(n-3) + 4(-n+11) a(n-4)
 + 6(-n+7) a(n-5) = 0`,
stated for all `n ≥ 9` (where `a(n-5)` is in the sequence's range, `n - 5 ≥ 4`).

A python3 check (dynamic programming over the walks): the definition reproduces the data and the
recurrence holds for all `9 ≤ n < 300`.

Conventions: a sequence is a function `Fin (n + 1) → ℤ`; `a(n)` is the cardinality
(`Set.ncard`) of the finite set of admissible sequences. The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a026086

/-- The admissible sequences `(s(0), ..., s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | s 0 = 0 ∧ s (Fin.last n) = 3 ∧ ∀ i : Fin (n + 1), 1 ≤ i.val →
    (i.val ≤ 3 → |s i - s ⟨i.val - 1, by omega⟩| = 1) ∧
    (4 ≤ i.val → |s i - s ⟨i.val - 1, by omega⟩| ≤ 1)}

/-- `a n = A026086(n)` for `n ≥ 4`. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 9`. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    ((n : ℤ) + 3) * a n + 5 * (-(n : ℤ) - 1) * a (n - 1) + 3 * ((n : ℤ) - 5) * a (n - 2)
      + (11 * (n : ℤ) - 9) * a (n - 3) + 4 * (-(n : ℤ) + 11) * a (n - 4)
      + 6 * (-(n : ℤ) + 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026086
